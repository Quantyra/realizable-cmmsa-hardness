# Complexity review, v1→v2 delta: SourceSize Spectral47 application

This is a static delta review, not final acceptance and not an overall GO. I used no tools, writes, Lean/Lake or subagents, and I recomputed no hashes; every hash below is copied from the packet. Both v2 files and Full101 are still uncompiled. This review can close the static syntax/composition finding, but it cannot provide native acceptance.

**Coverage**
- **Read fresh:** both v1 files and both v2 files (all four complete), both derivation JSONs, both complete original consumers (22DE415F…, AF3E380A…), the bridge (022E14E6…), the custody audit v2 and the MZ24 numbering audit.
- **Prior coverage, not reread:** the Full101 inhabitant body and earlier full-source reviews.

## 1. What changed from v1 to v2

| Item | v1 | v2 | Result |
|---|---|---|---|
| Theorem 1 inhabitant reference | `…ExactInhabitant.⏎ spectral47_exact_contract_inhabitant` | Joined on one line | ✓ |
| Theorem 2 inhabitant reference | Same split | Joined | ✓ |
| Checks `example` type | `…SourceSizeAnalyticMoment.⏎ Spectral47ExactContract` | Joined | ✓ |
| Checks `example` term | `…ExactInhabitant.⏎ spectral47_…` | Joined | ✓ |
| Parentheses around the `.mp` term | — | `((bridge c).mp (inhab c))`, balanced, then `a ha` (and `hkDyadic hkm` in theorem 2) | ✓ |
| Header comment, imports, opens, `autoImplicit`, `noncomputable section`, `Classical.propDecidable` | — | Unchanged | ✓ |
| Theorem names, binders, `let` telescopes, conclusions | — | Identical text | ✓ |
| Argument order passed to the consumers | `… hfail ⟨spectral⟩ a ha [hkDyadic hkm]` | Unchanged | ✓ |
| New declaration | — | `theorem sourceSize_spectral47_inhabited (cutoff) : SourceSize.Spectral47ExactContract cutoff := (spectral47_contract_iff cutoff).mp (inhabitant cutoff)` | ✓ |
| Checks file additions | — | Five `#print axioms` lines | ✓ |

The only differences are the four joins, the named theorem and the axiom checks. The statements and proof applications mean exactly what they meant in v1.

**Typing of the named inhabitant**
- `Spectral47ExactContract` sits on both sides of an `Iff`, so it is a `Prop`, and declaring it with `theorem` is correct.
- `.mp` turns the legacy-typed Full101 inhabitant into the SourceSize contract, which is the right direction. The bridge is `Iff.rfl`.
- The fully qualified names resolve from inside the candidate's namespace, because the relative lookup fails and falls back to root.

**Names in the `#print axioms` lines**
- `…SourceSizeSpectralApplication.sourceSize_spectral47_inhabited` matches the new declaration in this file.
- `…ActualFiniteAppendSpectral47ExactInhabitant.spectral47_exact_contract_inhabitant` matches the references in both theorem bodies. Its module is a direct import of the main file.
- `…SourceSizeOriginalApplication.selected_actual_material_moment_bound_original` and `…ManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent` match the namespaces of the complete consumer files.
- `…ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact` is the one inferred name (N3 below). It matches how the dyadic consumer refers to it, and it is in scope transitively through both consumers.

## 2. Guards and shared objects (rechecked against the complete consumers)

- **Rows stay independent of m:** `{N rows m L samplerA [k]}` and `I : Instance N rows`.
- **Shared objects:** `I copies U A C T f` go to the consumer unchanged. Inside the consumer `let`, `Cc/Tc/fc` are rebuilt from those same objects.
- **Selector and cutoff:** `hsel` uses `max (analyticSourceHeightFloor base sourceHeightCutoff j) (j+2)`. The inhabitant is instantiated at that same `sourceHeightCutoff`.
- **Failed-zoom guard:** `hrd`, `e`, `he` and `hfail` all apply to `selectedCoordinateLeafTable I copies U A T`. This is retained.
- **Positive-parameter guards:** `hA : 1 ≤ samplerA` and `ha : 0 < a` are retained. `hm : 0 < m` is derived inside the consumer.
- **Height, parity, ρ, split and dimension:** the consumer derives these internally from `selected_spectral_parameters` and `h² < J → hdim`. The candidate does not touch them.
- **Dyadic guards:** `hkDyadic` and `4m ≤ k` are retained, and `4 ≤ k` for HC46 is derived by `omega`. The fixed window `∃ k q, k = 2^q ∧ 4m ≤ k ∧ k < 8m` is retained in theorem 1.
- **HC46:** still supplied only inside the consumers, by `original_HC46_exact`. No legacy `Instance N m` material consumer is used.

## 3. Are the direct axiom checks adequate?

Yes. The five `#print axioms` lines show where each axiom comes from:

| Check | What its profile shows |
|---|---|
| The two candidates | The whole composition, transitively |
| `sourceSize_spectral47_inhabited` / Full101 inhabitant | The Spectral47 side alone |
| `original_HC46_exact` | The HC46 side alone |
| The two consumers | The chain before discharge, with `hSpectral` still a binder |

- **Bridge:** `Iff.rfl` has no axioms of its own and is native in Full100, so it needs no separate line.
- **Type-equality check:** the meta-level check proposed earlier (non-claims F6c) is not needed. The `exact` against each consumer is itself the kernel check that the candidate's type is definitionally equal to the consumer's type with `hSpectral` filled in. Since the text is also identical, the only remaining question is native elaboration.
- **Gate caveat:** `#print axioms` does not fail on `sorryAx`. The harness has to parse the output and reject anything outside `{propext, Classical.choice, Quot.sound}`, plus any "declaration uses 'sorry'" warning.

## 4. Disposition of prior findings

**My prior complexity report (complexity-01)**

| ID | Disposition |
|---|---|
| F1 (HIGH: split identifiers) | **CLOSED statically.** All four are joined and nothing else changed. A native parse/elaboration run must still confirm it. |
| F2 (Full101 dependency) | **OPEN, MEDIUM**, unchanged. |
| F3 (opens and instance context) | **OPEN, LOW**, unchanged. The compiler's `exact` settles it. |
| F4 (text type hashes) | **OPEN, LOW**, as an evidence tier. The type hashes are the same in v1 and v2, which is consistent because no statement changed. No meta-check is required (§3). |
| F5 (axiom profile) | **Improved.** The direct checks have been added; the gate still has to be enforced on real output. |
| F6 (scope: analytic RHS, fixed window vs P ≥ mT) | **OPEN, MEDIUM.** |
| F7 (claims boundary: no exact eigenvalue, 𝒢/Φ or adjoint) | **OPEN.** |
| §5 (bodies never supplied) | **RESOLVED as a supply claim for the 49 enumerated bodies.** The 49 entries' receipt paths all appear in `verified_receipts`, which is internally consistent. The inherited conditional verdicts still stand. Bodies reviewed in only one round (e.g. `ActualFixedFunctionalStarMoment`, `ActualMaximalPairLadder`, `ActualSourceStarLaw`) keep that round's verdict, conditions included. |

**Proof-adversarial report (P1–P8)**

| ID | Disposition |
|---|---|
| P1 | **CLOSED statically.** |
| P2 | **OPEN.** |
| P3 | **OPEN, LOW.** |
| P4 | **OPEN.** |
| P5 | **RESOLVED (supply)** for the 49 bodies. |
| P6 | **CLOSED statically.** Real output is still pending. |
| P7 | **OPEN, LOW.** |
| P8 | No action. |

**Non-claims report (F1–F10)**

| ID | Disposition |
|---|---|
| F1 | **CLOSED statically.** |
| F2, F3 | Remain resolved. |
| F4 | **OPEN, LOW.** |
| F5 | **OPEN.** |
| F6 | (a) and (b) **CLOSED statically**. (c) **WAIVED** per §3. |
| F7 (HIGH, claims boundary) | **OPEN.** |
| F8 | **RESOLVED (supply)** for the 49 bodies. |
| F9 | **OPEN, LOW.** |
| F10 | **OPEN.** The MZ24 audit pins the v4 source and gives a counter-derived A.10–A.13 (basis invariant, adjoint, Φ, eigenvalue). Claims share the lemma counter. The audit is source-only: the PDF was not confirmed and TeX was not run. M1 custody is therefore only partly closed. |

**Still open from earlier rounds:** all native and semantic debt, and R14 HIGH.

## 5. New findings in v2

| ID | Severity | Finding | Action |
|---|---|---|---|
| N1 | LOW | `derivation.json` v2 records type hashes only for the two theorems. The new `sourceSize_spectral47_inhabited` has no derivation row, and `only_type_change` does not mention that a declaration was added. | Add a row for the named theorem, or a note, in the next manifest. No source change is needed. |
| N2 | INFO | The unnamed `example` in Checks now duplicates the named theorem. | Harmless; it can stay. |
| N3 | LOW | The fully qualified name `…ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact` is inferred from how the consumers refer to it. That body (6F56EAF2…) is covered by the custody audit but is not in this packet. | If the name is wrong, only the Checks file fails. A native run confirms it. |
| N4 | LOW (inventory) | The audit covers the 49 bodies it selected by name and prefix. The candidate's statement also uses constants that are probably defined in modules outside those 49, for example `GrassmannCounting.Grass`, `ActualSelectedComplementSourceSizeAnalyticMoment` (`analyticSourceHeightFloor`, `selected_actual_source_dimension_bound`, `selected_actual_analytic_rhs`, contract, material bound), `ActualFixedFunctionalAppendOperator`, `ActualFixedFunctionalBinaryMatrixMoment`, `BinaryMatrixFourier`, `ActualAppendFourierCrossLevelOrthogonality`, and the legacy `ActualSelectedComplementAnalyticMoment`. Earlier rounds re-consulted the SourceSize contract and material bound. This packet does not show whether the rest are in the earlier 41-body reuse set. | Produce a crosswalk from each statement-level constant to its module and receipt. Only a module that is in neither the 49 nor the 41 is a real gap. No duplicate reviews otherwise. |

## 6. Complexity lens

Nothing in the complexity picture changes. The candidates are still pure proof-term composition plus one universal `Prop` inhabitant: there is no algorithm, sampler, encoding, reduction or runtime content. J = `blocks samplerA h` and k are still fixed parameters, and encoded size is not addressed.

## 7. Remaining to-do list

1. Renew GCP authentication. Compile frozen Full101 unchanged, then the v2 main and Checks files as a separate capture, with no Full101 edits.
2. Gate on the real output: the parse and the `exact` elaborations succeed; each of the nine `#print axioms` outputs (the five new lines plus the two candidate theorems' profiles printed twice) is a subset of `{propext, Classical.choice, Quot.sound}`; there is no sorry warning; owned warnings are counted.
3. Trace actual consumption, recording both discharges in one trace: Full101 inhabitant → bridge → SourceSize consumers → `original_HC46_exact`. Confirm no legacy material theorem appears.
4. N1: add the manifest row for the named theorem. N4: produce the constant→module→receipt crosswalk.
5. Keep the claims boundary (F6/F7/P4) as stated:
   - the result is a bound against `2·selected_actual_analytic_rhs`;
   - only the dyadic theorem fits P ≥ mT;
   - the exact eigenvalue, 𝒢/Φ and the adjoint are not established;
   - the MZ24 numbering still needs PDF confirmation.
6. Keep open:
   - the scalar steps downstream of the RHS;
   - numeric NO;
   - the source/star/robust8S/pre-draw witnesses;
   - sampling, encoded reduction, runtime and learning;
   - upstream transports;
   - R14 HIGH;
   - warnings, fresh-checkout and custody replay;
   - novelty, citations and PDF;
   - the provider and QA gates;
   - publication.
