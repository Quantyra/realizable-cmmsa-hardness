# Complexity review, packet 5 of 5 (Full90 material consumer)

## Verdict: GO-WITH-NOTES, for this packet only

All 24 supplied file bodies were inspected and none was skipped. I found no defect that blocks the packet.

This verdict does not cover:
- the selected material root;
- the Complexitylib boundary, because none of its 23 bodies is in this packet;
- the whole manuscript.

None of these 24 files was among the 169 bodies that could be reused under the identity audit; every one is new or changed. So this is a fresh review, not a reuse of an earlier report.

**How I reviewed it.**
- I read the source text only. I used no tools, made no writes, ran no Lean or Lake, and started no subagents.
- Compilation, the 173 standard root profiles and the source pins come from the qualified native receipts. I did not reproduce them or recompute any SHA256.
- Findings name declarations rather than line numbers, because I can't count lines reliably without tools.
- I checked these files for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` and `opaque`, and found none.

**Axiom coverage is narrow.**
- 20 of the 24 modules are pinned `transitively_consumed: false`. Their declarations have compile evidence only and no fresh axiom profile.
- Four modules are consumed: MatrixGrassmannIdentity, SamplerParameters, PortCycleReplacement and TaggedFinite3LinSource. Within them, only the constants a root actually reaches are covered, and no list of those constants was supplied.

## File inventory

| # | File (SHA prefix) | Consumed | Status |
|---|---|---|---|
| 1 | GaussianNearOne (EAE0FEAD) | no | inspected |
| 2 | GaussianRatio (C2FC1E27) | no | inspected |
| 3 | GoodAdvice (8FFD7284) | no | inspected |
| 4 | GrassmannIncidence (575AC1E2) | no | inspected |
| 5 | **MatrixGrassmannIdentity** (EA286521) | **yes** | inspected |
| 6 | **PortCycleReplacement** (B0E8FCA2) | **yes** | inspected |
| 7 | PosteriorDensity (61C4696B) | no | inspected |
| 8 | PosteriorReweighting (85284AA3) | no | inspected |
| 9 | RobustSourceLineContainment (D97FCE89) | no | inspected |
| 10 | **SamplerParameters** (4DA1946F) | **yes** | inspected |
| 11 | SamplerProximity (8B2FDBD6) | no | inspected |
| 12 | SubmoduleFunctionalGluing (0D11251A) | no | inspected |
| 13 | SubspaceRestriction (A50125D2) | no | inspected |
| 14 | **TaggedFinite3LinSource** (D2145BA0) | **yes** | inspected |
| 15 | TaggedQuestionMassBridge (B258BB7F) | no | inspected |
| 16 | TripleRestrictionDimension (D21F2235) | no | inspected |
| 17 | TripleRestrictionRank (8F86EE5F) | no | inspected |
| 18 | VectorAdvice (AA11F987) | no | inspected |
| 19 | WeightRounding (AE759923) | no | inspected |
| 20–24 | ZoomOutIncidence / Joint / Parameters / Posterior / Transfer | no | inspected |

## Complexitylib boundary from this packet

- **What this packet depends on.** Only PortCycleReplacement touches Complexitylib. It imports `Complexitylib.Classes.PCP.Internal.Expander` and builds a `Complexity.RegGraph`, using its fields (`V`, `D`, the decidable-equality, fintype and nonempty instances, `rot`, `rot_involutive`) plus `deg` and `order`.
  - `graph_degree` and `graph_order` close by `change … Fintype.card …`, which shows `deg` and `order` unfold definitionally to `Fintype.card D` and `Fintype.card V`.
  - Nothing in this packet uses `ExpanderFamily`, a spectral gap, Cheeger, mixing or random-expander existence. Expansion enters only as the explicit hypothesis `hexpand`.
- **What is not done here.** The bodies of RegularGraph, Union, NumEnc and Expander are not in this packet, so this packet does not review them. The Complexitylib obligation stays open for integration (see B-1).

## Core audit (checked by hand)

### MatrixGrassmannIdentity (consumed)

The moment identity holds as stated:
- **Matrix moment.** `matrix_grassmann_identity` gives E_M[g(M)·T_F(M)^t] = α·E_{R, t iid L⊇R}[…]. Here α = ρ(n,0,d)·ρ(n,d,w)^t, and ρ(n,d,w) = ∏_{i<w}(1 − 2^{d+i}/2^n).
  - It holds for every t, including t = 0, under the guard d+w ≤ n.
  - The base factor is exact: |Grass|·frameProduct(d,d)/|V|^d = ρ(n,0,d).
- **Rank event.** `rankEventProbability_eq_alpha` shows α equals the probability of the actual joint rank event.
- **Loss bound.** `alpha_loss_bound` gives 1 − α ≤ (d + t·w)·2^{d+w−1}/2^n, via the union bound (`product_failure_le`) and 1 − ρ^t ≤ t(1 − ρ).
- **Which direction is free.** The bound matrix ≤ Grassmann follows from α ≤ 1 with no further premise. The reverse, Grassmann ≤ 2·matrix (`grassmann_le_twice_moment`), needs the explicit size premise `hsmall`.

### SamplerParameters (consumed) and SamplerProximity

**Basic facts in SamplerParameters.**
- `blocks A h = 2^(2^(A h²))` and `beta = A h²/blocks`, with 0 ≤ β < 1.
- The mean identity `blocks·beta = A h²` is exact.

**Arithmetic in the proximity lemmas.** I re-derived each step:
- `eventually_ready` needs C = 4(A + 4r + 212), because 2r + r + r = 4r and 200 + 2 + 10 = 212.
- `ready_advice` needs exp/2 ≥ mean + 100h² + a + 4.
- `ready_zoom_scaled` needs mean/2 − exp/4 + 2h + 5 ≤ −100h².
- `ready_density` needs 3 + 2a·h⁴ + c + mean − exp ≤ −30h², with a, c ≤ r.
- `five_decay70_lt` holds because decay70 = decay20·decay50 and decay50 ≤ 1/8.

**Quantifier order.** A and r are fixed first, then ∃N, then ∀h ≥ N, then ∀a, c ≤ r. This is honest.

### PortCycleReplacement (consumed)

- **Construction.**
  - `rotation_involutive` holds for every degree d+1 ≥ 1. When d = 0, labels 1 and 2 form a self-loop pair; when d = 1, they form parallel edges.
  - `cut_decomposition` (cut = external + cycles) is exact.
- **Rounding steps.**
  - `minority_le_cycle` is weak but correct.
  - `smallSide_transport` holds, and `external_transport` holds through the bijection given by R.
- **Main bound.** I checked `cut_expansion` by hand: h·small(S) ≤ (d+1)·cut + ((d+1) + h)·B, with B ≤ (d+1)·cut. That gives the constant h/((d+1)(d+2+h)).

### TaggedFinite3LinSource (consumed) and TaggedQuestionMassBridge

- **Tagged copies.** Rows stay injective. Violations are additive across copies, and repeating an assignment costs exactly K·viol.
- **Tuple counts.** The tagged tuple equivalence is exact, and the base-projection event count is K^J·|A|.
- **Conflicts.** A tagged conflict holds iff the tags are equal and the base rows conflict. So the bad-tuple mass is at most J(J−1)C/(K·|Row|).
- **Edge cases.** J = 0 and K = 0 are handled. The rational J−1 is cast correctly.

### Sampling and posterior chain (not consumed)

**Restriction draw.**
- In TripleRestriction*, each block is kept whole with probability 1−β, or a single coordinate k is kept with probability β/3; blocks are independent.
- The retained dimension is exactly 3J − 2·drop.
- `badRows_probability` gives the union bound (2^c − 1)·β, and the codimension identity holds on the good event.

**Posterior estimates.**
- PosteriorDensity's density 8·2^{2aT} follows from G(3J,a)/G(dim retained,a) ≤ 2·2^{2a·drop}, using `normalizedFrame` ≥ 1/2.
- Fixed W is valid with no independence assumption, because W is chosen after Q and before the draw s.

**Generic reweighting.** The error bound 4η + 4ζ/p₀ in `normalized_reweighting` checks out.

**Zoom-out numerics.**
- `numerical_small` gives 12·q20 < q12.
- `total_error_small` gives 8·q20 + q12 < q10.
- `ready_transfer` gives TV ≤ 4·q100/p₀.
- ZoomOutJoint reaches C/8 as C/4 − 2ζ.

**Robust containment.** RobustSourceLineContainment's quotient equivalence, the union over lines and the dyadic 2^{−(n−j−d−1)} bound are all correct.

**Null-event conventions.** Null events and fibres evaluate to 0 rather than being renormalized. The resulting mass defect is bounded explicitly by `conclusion_mass_defect`.

## Findings

| ID | Sev. | Declarations | Finding and disposition |
|---|---|---|---|
| C5-1 | Medium (integration) | `SamplerParameters.blocks`, all Sampler*, GoodAdvice, ZoomOut*, VectorAdvice | The ambient dimension is 3·2^(2^(A h²)), doubly exponential. Every result here is a finite probability fact. No size, encoding or runtime claim exists or can be derived from these files. Since SamplerParameters is consumed, any consumer that treats h or `blocks` as polynomial in the input size must prove that elsewhere. **Retained**; the runtime and encoded-reduction gates stay open. |
| C5-2 | Low | `SamplerProximity.eventual_inner_domination`, `eventually_ready`, every `eventual_*` | Thresholds come from `Tendsto`/eventually, so N(A,r) exists but has no explicit value. Usefulness of the parameters and the numeric NO bound needs explicit thresholds. **Retained.** |
| C5-3 | Medium (non-claim) | `ZoomOutJoint.ready_joint_success`, `eventual_joint_success`, `VectorAdvice.decoder_event_transfer` | The decoder (F, W, f, with agreement ≥ C) is the hypothesis `hdecoder`, alongside `hdelta` and `hrank`; no decoder is proved to exist. The factor (mass F − mass bad − TV) can be negative, which makes the bound trivial. **Conditional only.** |
| C5-4 | Medium (boundary) | `PortCycleReplacement.cut_expansion`, `graph` | Expansion of the input graph is the assumed `hexpand`, stated in the local `external`/`smallSide` form. The local `cut` is not shown equal to any Complexitylib cut, expansion or Cheeger notion. The constant degrades like Θ(h/d²). **Retained**, plus B-1. |
| C5-5 | Low | `PortCycleReplacement.table`, `table_length` | `table` shows computability and its length n(d+1)·3. R is an arbitrary function with no cost model, so this gives no polynomial-time or FP claim. The docstring says so. |
| C5-6 | Low | `WeightRounding.polynomial_denominator_bound`, `rounding_sound`, `dyadicScale_upper` | The denominator bound 17(n+1)^{k+1} is conditional on the supplied premise 1/t ≤ (n+1)^k. Dyadic padding stays below 2× the threshold only when t ≤ 1. The floor-half loss makes sig = 1 degenerate (budget 0). This is a size bound only; the header disclaims runtime. **Retained.** |
| C5-7 | Low (provenance) | UNCOMPILED / SOURCE DRAFT banners in GaussianNearOne, GaussianRatio, GoodAdvice, GrassmannIncidence, MatrixGrassmannIdentity, PortCycleReplacement, PosteriorDensity, SamplerParameters, SamplerProximity, TripleRestrictionDimension, VectorAdvice and all five ZoomOut* files | These conflict with the native compiled closure. They carry no weight as evidence in either direction. Fix them before the render gate. |
| C5-8 | Low (hygiene) | Implicit binders (a, b, c, J, n, m, T) in GaussianNearOne, GaussianRatio, GrassmannIncidence, PosteriorDensity, TripleRestriction*, SubspaceRestriction and `GoodAdvice.bad` | These files rely on autoImplicit. The statements are universal, so nothing is weakened. |
| C5-9 | Info (axiom scope) | All 20 unconsumed modules | Compiled, but with no fresh axiom profile. Do not credit them as standard-axiom results. |
| C5-10 | Info | `grassmann_le_twice_moment` vs `matrix_grassmann_identity`/`alpha_bounds` | Integration should confirm the material consumer uses the free direction (matrix ≤ Grassmann) and discharges d+w ≤ n. |
| C5-11 | Info | TaggedFinite3LinSource | The file gives additivity and the repeat value, but does not state that the tagged optimum equals K·(base optimum). That is immediate from additivity, but any NO-preservation use must derive it. The sizes are K·\|Row\| and K·\|Var\|. |
| C5-12 | Info | `GoodAdvice.Properties` fixed-W clause | The binder Q ≤ W is unused, so the clause is stronger than stated. There is no union over W. |

## Questions for integration

1. **B-1, Complexitylib.** Review the bodies of RegGraph, `deg` and `order` (RegularGraph, Union, Expander, NumEnc). If any consumer needs expansion of `PortCycleReplacement.graph` itself, a bridge from the local `cut` to Complexitylib's definitions is required. Also confirm whether FixedPortCycleFamily or ExpanderCutInstantiation discharges `hexpand`, or whether it stays an explicit hypothesis.
2. **Reached constants.** List the reached constants of the four consumed modules and say which roots reach them, including whether the material root reaches `cut_expansion`, `grassmann_le_twice_moment`, or the tail lemmas in SamplerParameters.
3. **External statements relied on but not supplied in this packet.**
   - MatrixGrassmannFibre, Incidence and Moment, and CoveringSpan: `card_rankArray`, `sum_over_rankArrays`, `uniform_extension_law`, `split_arrays`, `sum_over_frames`, `card_internal_frame`.
   - GrassmannCounting.
   - GrassmannFlagPosterior: `flag_product`, `card_upper`, `card_relativeUpper`, `upperQuotientEquiv`, `containmentProbability`, `retainedConditional`, `incidenceCount_eq`.
   - AdviceExceptions, ConditionedCovering and CoveringTV: `exceptional`, `badZoom`, `adviceTV`, `conditionalDistance`, `deletedConditional`, `fibre_conditional_tv_le`, `retained_failure_le`, `failureFraction`.
   - DropTailParameters, FiniteSampling, Finite3LinSource, ActualQuestionMassBridge (`rowConflict`) and Formula.
4. **Material export.** The body and guards of `selected_actual_material_moment_bound_original` are not in this packet. The questions are whether it is the same material theorem with only `hHC` removed, and whether `hSpectral`, the selector, failed zoom, strict rank and positivity premises are still present. That must be verified against the packet that holds those bodies, not the selected-leaf wrapper.

## Safe conditional claim

Under the qualified native receipts and the pinned kernel and library trust, these 24 files prove the finite identities and bounds stated above:
- the exact matrix–Grassmann incidence moment, with guard d+w ≤ n;
- the exact tagged-copy additivity and the conflict dilution by K;
- the doubly exponential sampler family, with eventual, non-explicit thresholds;
- the posterior, zoom-out and transfer chain, conditional on good advice, a fixed W and an assumed decoder;
- port-cycle cut expansion, conditional on the assumed input expansion `hexpand`.

**Not claimed:** runtime, encoding size or FP; decoder existence; Complexitylib acceptance; spectral expansion; explicit thresholds; useful numeric NO bounds; standard axioms for unreached declarations; material acceptance; manuscript fidelity; any whole-manuscript verdict.
