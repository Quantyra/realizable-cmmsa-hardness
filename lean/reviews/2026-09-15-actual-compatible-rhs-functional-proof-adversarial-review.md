# Actual-compatible RHS-functional proof-adversarial review

Date: 2026-09-15  
Repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp`  
Reviewed commit: `f740e503c3e357e9329fd5e6bbd1809ae0d26d37`  
Disposition: **GO-WITH-NOTES**

This is a read-only top-level proof-adversarial review of the frozen `ActualCompatibleRhsFunctional` main-and-Checks increment and its target-fresh certification evidence. It covers construction of a coordinate-space RHS functional, construction and uniqueness of the compatible equation-span RHS functional, use of `LinearMap.exists_extend`, the supplied-coordinate-functional assumptions, fixtures, axiom output, forbidden-source scan, and the postprocessing recovery. It does not review label objects, full label transport, an actual star carrier, star acceptance, stationarity, randomized-reduction assembly, or any hardness conclusion.

## Frozen sources and certification binding

The inspected checkout is exactly the assigned commit. The reviewed sources have these SHA-256 values, matching `post-run-validation.txt` and the before/after source inventories:

- `ActualCompatibleRhsFunctional.lean`: `5173EA699D41D0305508376F9EDEE99F8202FCD8C8EC134021BEE78366CD65CB`.
- `ActualCompatibleRhsFunctionalChecks.lean`: `F3E5525D5BEACFFB2329E91377293DD1F781E6EB8F45C2DB3395BB40BA455ADA`.

The closeout record has SHA-256 `9967119CD33907D199504355F6C170C60413A4C9F13573E2F4FAC2F501D0E313`. The canonical 49-row artifact manifest has SHA-256 `D51204172B84D74FEC19BB6C34A6245F69AA4FF3A3D42EEE1A471261DFE21A30`, matching `artifact-hashes-manifest.sha256`. I independently rehashed all 49 rows: every artifact exists and there are zero size or hash mismatches. `source-before.sha256` and `source-after.sha256` are identical.

The dedicated target contained none of the seven rebuilt project objects before the run. The certification rebuilt support, span intersection, finite source, RHS construction, side-condition agreement, main, and Checks sequentially with Lean `4.34.0-rc2` and `LEAN_NUM_THREADS=1`. All seven exit receipts record `exit_code=0`. The principal new object hashes are:

- `ActualCompatibleRhsFunctional.olean`: `C7D44C65E4D790D0319A9C8295CB5C6B63446C501F79A3F1131D5A72E4EA124D`.
- `ActualCompatibleRhsFunctionalChecks.olean`: `5BBF75A4E8736747AEB15807894A279E2867DA064223157527F7383631807F64`.

This is a target-fresh rebuild of the complete local dependency chain named above against seeded, hashed transitive dependencies. It is not a from-source rebuild of all Mathlib or every project module, and the certification states that boundary correctly.

## Exact statements and assumptions

`actual_exists_coordinateFunctional` assumes an actual occurrence-allocation instance, a finite row set `U`, and `GoodQuestion I.support U`. It concludes that there exists a linear functional on exactly `coordinateSpace I.support U` which maps every selected equation vector to `I.rowRhs e`. It does not assert uniqueness of this coordinate-space functional.

`actual_existsUnique_compatibleRhsFunctional` assumes two good questions `U` and `U'`, a supplied coordinate-space linear functional `f` on `U`, and the exact premise that `f` maps every equation vector selected by `U` to its actual row RHS. It concludes that there is a unique equation-span linear functional `g` on `U'` satisfying both:

1. `g` maps every equation vector selected by `U'` to its actual row RHS; and
2. `f` and `g` agree on `equationSpan I.support U' \u2293 coordinateSpace I.support U`.

No satisfiability, source assignment, overlap consistency, nonempty intersection, label, probability, or computational premise is added. The supplied `f` premise is real and visible in the signature; existence of such an `f` is separately discharged by `actual_exists_coordinateFunctional`.

## Adversarial proof analysis

### Coordinate-space existence and `exists_extend`

The proof first obtains the certified unique RHS functional `psi` on `equationSpan I.support U`. `LinearMap.exists_extend psi` supplies an ambient linear map `F` whose restriction to that equation span equals `psi`. The proof then defines `f` by composing `F` with the subtype inclusion of `coordinateSpace I.support U` into the ambient function space.

For each selected equation vector, the proof packages that vector as an element `v` of the equation span and applies the extension equality pointwise with `LinearMap.congr_fun hF v`. The resulting ambient equality rewrites the value of `f`; the previously certified generator equation for `psi` supplies `I.rowRhs e`. The subtype domains and coercions line up exactly, as confirmed by the frozen compile.

This use of extension is mathematically legitimate over `ZMod 2`. It proves existence only. It does not make the coordinate-space extension unique, canonical, executable, or polynomial-time computable. The dependence on `Classical.choice` is visible in the axiom profile and must not later be described as an efficient label-generation algorithm without an additional constructive argument.

### Compatible equation-span functional

For `U'`, the proof obtains `g`, its generator equations `hg`, and uniqueness `hunique` from `actual_existsUnique_rhsFunctional`. It applies the already-certified actual side-condition agreement theorem to `f`, `g`, `hf`, and `hg`, obtaining agreement on the exact span/coordinate-space intersection.

The uniqueness obligation for the conjunction is handled by projecting `hg'.1` from any competing witness and applying `hunique`. This is sound: RHS generator values already uniquely determine a linear map on `equationSpan I.support U'`, so the intersection-agreement conjunct does not need a separate uniqueness argument. The conclusion's uniqueness is correctly limited to `g` on the equation span. It does not claim uniqueness of `f`, uniqueness of an ambient extension, or uniqueness of a full manuscript label.

The empty-question cases are sound. For empty `U`, extension starts from the unique map on the zero equation span and yields at least one coordinate-space map. For empty `U'`, the equation-span witness is unique and the certified agreement theorem handles the intersection. No hidden nonemptiness premise is required.

## Axioms and forbidden constructs

The frozen-source scan reports no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit axiom declaration. Direct inspection found no unsafe shortcut or weakened restatement. `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for both reviewed theorems. These are standard Lean/Mathlib axioms in this development; no project-specific axiom appears.

The four recorded warnings come only from unused section variables in pre-existing dependency declarations. Main and Checks emitted no warning.

## Fixture assessment

The Checks module prints both exact signatures and axiom profiles. Its nonempty `Instance 1 1` fixture has RHS `1`, proves the row set is a good question, obtains `f` from `actual_exists_coordinateFunctional`, and then invokes `actual_existsUnique_compatibleRhsFunctional` at its exact signature. This is not an empty or zero-RHS fixture, and it confirms that the two theorems compose without an extra premise.

The fixture remains a type-level consumption test: it does not evaluate the selected extension, compare two distinct good questions, or exercise a nontrivial proper intersection. The separate empty fixture checks only coordinate-functional existence. A later label-gluing consumer should provide the stronger behavioral fixture, preferably with distinct questions and a nonzero common equation vector. This coverage limitation does not undermine the universally quantified kernel-checked proofs.

## Postprocessing diagnostic

The initial evidence-wrapper postprocessing exited `1` because PowerShell did not create `finite.combined.log` when both constituent raw logs were empty. The recovery created empty combined-log files for stages whose raw stdout and stderr were both empty, then reran only evidence postprocessing. The certification status explicitly records `rerun_compile=false`. The retained raw logs, seven successful exit receipts, immutable source hashes, and fresh object hashes bind the Lean result independently of that bookkeeping issue. The diagnostic therefore does not invalidate the certification.

## Findings and disposition

No proof gap, theorem weakening, hidden mathematical premise, false uniqueness claim, misuse of `exists_extend`, domain-coercion error, forbidden construct, project axiom, fixture vacuity in the principal nonempty example, or evidence-binding defect was found.

The disposition is **GO-WITH-NOTES**. The notes concern scope and later consumers:

- the coordinate-space functional exists nonconstructively and is not unique;
- the compatible theorem accepts a supplied `f`, while the Checks module separately composes it with the existence theorem;
- uniqueness is only for the equation-span functional `g`;
- no effective or polynomial-time label-generation procedure follows from `LinearMap.exists_extend`;
- the fixture does not yet test distinct questions with a nontrivial common vector.

This increment closes the local compatible-RHS-functional bridge. Its next consumer should define the manuscript's actual side-conditioned label or gluing object and state exactly how the coordinate-space map and equation-span map combine. The remaining path is:

```text
compatible RHS functionals
  -> actual label/gluing object and minimal transport
  -> actual star carrier and acceptance
  -> resampling kernel and stationarity
  -> source-to-star acceptance coupling
  -> randomized-reduction assembly and runtime
  -> quantitative consumers and headline hardness theorem
```

