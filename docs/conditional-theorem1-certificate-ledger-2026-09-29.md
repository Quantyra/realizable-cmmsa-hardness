# Conditional core Theorem 1 certificate ledger (2026-09-29)

**Verdict: conditional core certificate incomplete.** This ledger identifies the cited
inputs and the manuscript-new obligations. No source-to-CMMSA reduction is an
imported theorem, and no current Lean theorem proves the complete manuscript
Theorem 1 from only the six cited contracts below.

## Exact target and quantifiers

The target is [Theorem 1](../paper/body.tex), Section 1: functions
`σ_L : ℕ+` and `γ_L ∈ (0,1)` with `log σ_L / log L → 1` and `γ_L → 0`, such
that **for every sufficiently large fixed integer `L`**, one uniform
randomized polynomial-time many-one reduction on all input instances gives
realizable `Gap^{0,γ_L}_{σ_L} F[L]`-CMMSA, with success at least `2/3` on each
YES or NO input. The polynomial exponent may depend on fixed `L`. The output
weights and budget have a polynomial-magnitude common denominator. It does
not assert one polynomial exponent uniform in `L`.

The manuscript fixes `m, ξ, ρ, A, h, J=2^(2^(Ah²)), β=Ah²/J` and alphabet
`R=2^(2h)` before choosing an **arbitrary fixed positive** PCP completeness
target `τ`. It then chooses a fixed positive outer YES error
`ε₁ ≤ τ/[100(m+1)J]`. The outer NO gap and `κ` must not depend on this later
`ε₁`. For each target `L`, the parameter selector must use the *actual*
fixed-parameter lower cutoff `h_min(m,ξ,A,...)`; the existing
`ActualCertifiedManuscriptParameters.certifiedM` uses `n+2` as a placeholder
source floor and therefore does not by itself certify this quantifier.

## Six external contracts, source scope, and Lean status

| Cited contract | Source checked scope | Lean status |
| --- | --- | --- |
| Outer hardness and smooth repeated game | MZ Theorem 3.1, Section 3.2, Claim 3.2; fixed absolute 3-Lin NO gap, arbitrarily small fixed positive YES error, bounded occurrence, and game value `≤2^{-Ω(η² 2^{-r} βJ)}`. Manuscript Section 3, `paper/body.tex:55`. | **Typed, visibly external contract** in `ActualMZOuterSourceContract.ExternalMZOuterSource`; no inhabitant is proved. It fixes absolute `s<1` and `κ>0` before the later arbitrary `ε₁`, includes an encoded zero-coin FP SAT reduction, exact indexed product law and strategy value fields. The fixed encoding/parser and MZ game bounds are still external. Source union/concatenation notation requires a separate observation bridge before this product-game value can bound the manuscript decoder. See `docs/mz-outer-source-contract-2026-09-29.md`. |
| Star construction and label transport | MZ Section 3.3, Lemmas 3.3–3.4; legitimate `U`, transverse `K,L_i`, side-condition-preserving unique transport, weighted `(m+1)`-star, finite enumeration. Manuscript `paper/body.tex:57`. | **External** for construction/transport. Tagged physical-law and representative-selection Lean modules prove selected new comparisons, but do not construct the full encoded reduction. |
| Scoped local decoder | MZ Theorem 4.2; fixed `U`, density at least `S=2^{-2(1-1000ρ)hm}`, `a+c≤10m/ρ`, lucky `Q` mass at least `2^{-6h²}`, and agreement `C=2^{-2(1-1000ρ²)h}/5`. MZ v1 Section 5.1 equation (8) fixes its PCP application's schedule `J=2^(100h²)`; Theorem 4.2 itself does not state that equality. Manuscript `paper/body.tex:59` changes the schedule. | **Typed, visibly external source-law interface** in `ActualMZFixedUSourceDecoderContract.ExternalMZFixedUSourceDecoder`; no inhabitant is proved. Its cutoff precedes `h,J,U` and both tables; this interface is conservatively restricted to the cited source PCP schedule. The fixed-`U` transverse law and exact real thresholds are typed. The changed-ambient robust `8S` application remains manuscript-new and cannot be obtained by instantiating this interface at the manuscript `J=2^(2^(Ah²))`. |
| Maximal-pair counting | MZ Definition 5.4 and MZ24 revision 1 Theorem 5.26, with `δ=ρ/m`, fixed subsidiary constants, `dim V≥2^h`, dimensions/codimensions `≤10m/ρ`, threshold `B≥2^{-2(1-(ρ/m)^3)h}`, and count `≤B^{-2}2^{O_{m,ρ}(h)}`. Manuscript `paper/body.tex:61`. | **External**. The descending threshold ladder and use in changed ambient are manuscript-new. |
| Covering | KMS Definition 4.5, Lemmas 4.6–4.7, Section 8; independent triple-deletion sampler and its joint-law conditioned advice bound, including exceptional `Q` mass. Manuscript `paper/body.tex:63`. | **External**. The posterior, vector-law and zoom-out comparisons for this parameter order remain manuscript-new. |
| Weighted star compilation | HN Definition 4.4 and Lemma 4.6; one global center/leaf partition, `m≥1`, deletion of zero-occurrence vertices, normalized occurrence weights, repeated leaf-variable consistency, leaf bound `(m+1)R`, budget `1/Λ`, exact-weight YES, monotonicity, and real-threshold base NO satisfaction at most `3/4`. Manuscript `paper/body.tex:65` and Section 8. | **Typed external finite-semantic contract** in `ActualCoreSourceContractScopes.ExternalHNWeightedStarCompiler`, uniformly over valid finite stars; no inhabitant is proved. Its `HNSourceStar` preconditions enforce the source applicability scope, and `HNCompilationConclusion` uses the actual finite `compile`/weight semantics. The polynomial-time encoded formula-distribution constructor is absent. This contract does not supply AND sampling, finite-list repair, rounding, or an encoded source-to-CMMSA map. Strict `<γ_L` is obtained only downstream. |

These entries describe mathematical source contracts, not Lean axioms.
The outer MZ product game, fixed-`U` decoder, MZ24 count, and finite-semantic
HN compiler have explicit external Lean interfaces; faithful typing of the
remaining source contracts and encoded interfaces remains work. A broad `hSrcCmmsa` parameter would absorb
manuscript-new work.

The fixed-`U` contract is an external *source test-law* boundary, not a
manuscript decoder theorem. `ActualTaggedMZSideDraw.conditionalCanonicalDensity_eq_side`
already identifies the selected tagged conditional density with the typed
source side law for the same fixed `U,C,T'`. A proof must still justify that
the typed tagged domain represents the source question and leaf alphabet,
the `SideCenter`/`SideLeaf` nonempty hypotheses follow from the tagged
fibres, the selected table is legalized at each fixed `U` so that
`SourceLeafTableLegal` holds without decreasing density, and the changed-ambient
inverse and robust `8S` result at the manuscript `J`. Supplying a source
contract inhabitant does not discharge those new obligations. The source text writes the output probability over `Q⊆L⊆W`
without repeating transversality; the Lean `SourceZoom` conditions on
transverse leaves, matching the defined source leaf alphabet and manuscript
description. The equality of that conditioned output with the source's
printed `Q⊆L⊆W` probability is an unresolved source-alignment proof
obligation, not an established convention.

## Lean facts already available for the manuscript-new comparison

- `ActualTaggedCanonicalNoComparison.tagged_physical_le_canonical_plus_collision`
  selects one predraw representative table for an arbitrary fixed legal table
  with explicit class-collision loss. The conditioned original-score bridge
  and `ActualTaggedFixedUDensityForce.ordered_manuscript_half_value_forces_MZ_threshold_U`
  feed the fixed-`U` robust input. `ActualMZFixedUSourceDecoderContract.selectedDomainTable_sourceLegal`
  proves that the same predraw representative table satisfies the source
  leaf side conditions on every transverse leaf at each eligible fixed `U`.
  These facts do not prove a decoder conclusion.
- `ActualModifiedPcpParameterOrder` proves `βJ=Ah²` and the basic reciprocal
  exponent comparison. The new
  `ActualConditionalTheorem1Core.outerYesError_pos`,
  `conditioned_honest_failure_lt`, and `conditioned_outer_lt_decoded` prove
  the late positive `ε₁` choice, conditioned YES failure `≤τ/75`, and the
  factor-two strict NO numerical inequality under `20<κA` and `h>0`.
  Here `κ : ℝ` is arbitrary positive, as in the cited outer contract;
  `exists_outer_repetition_scale` chooses a natural `A` **after** `κ` and
  **before** `h`. The bound uses real `2^{-κAh²}`, with no integrality
  assumption on `κ`.
  `no_strategy_from_outer_and_changed_ambient` states the resulting
  contradiction with the changed-ambient decoder success as an **explicit
  new premise**. `lake build PvNP.RealizableHardness.ActualConditionalTheorem1Core`
  passed (3222 jobs), and the separate `ActualConditionalTheorem1CoreChecks`
  passed with only `propext`, `Classical.choice`, and `Quot.sound` axioms.
- `ActualCertifiedManuscriptParameters` proves the `/16`, `/4`, `/2` gap
  chain and asymptotic family for its current selector, whose
  `manuscriptSourceFloor n = n+2` is a placeholder. The separate
  `ActualLedgerSelectedParameters` proves eventual selection, sigma budget,
  gamma decay, four-label room, and `log σ_L/log L → 1` for every *fixed*
  `SourceHeightBounds` ledger. It also chooses `A` after each positive real
  `κ`, then selects a ledger and eventual input lengths. The seven ledger
  cutoffs are explicit external numerical data; their sufficiency for the
  inverse, robust-history, covering, posterior, maximal-count, outer-decoder,
  and compilation source claims has not been proved.
- `ActualTheorem1.theorem1_realizable_cmmsa` composes assumed SAT-to-source
  and source-to-CMMSA `Preserves (1/6)` maps with Cook–Levin. It is a
  conditional assembly theorem; its broad source-to-CMMSA premise is **not**
  one of the cited contracts and does not certify the core result.

## Remaining manuscript-new obligations before core closeout

1. Prove the changed-ambient robust `8S` local decoder application using a
   separate changed-ambient inverse and amplification argument. The scoped
   MZ fixed-`U` contract is a cited source input and cannot be directly
   instantiated at manuscript `J`. Include all matrix-lift, inverse-explicit,
   positive-rank, posterior, and zoom comparisons needed for its exact query
   law and quantified `a,c,Q,W,g` conclusion. Precisely: for each fixed
   `m≥2`, `ρ>0`, positive `A`, and all sufficiently large admissible `h`
   chosen after them, set `J=2^(2^(A h²))`. For every eligible fixed `U`,
   fixed center table `C`, and predraw selected legal leaf table `T'`,
   side-test density at least `8S`, with `S=2^{-2(1-1000ρ)hm}`, must give
   **one fixed pair** `a,c` with `a+c≤r=10m/ρ` and at least `2^{-6h²}`
   of uniform `a`-spaces `Q`, each admitting `W⊇Q+H_U` of codimension `c`
   and a side-respecting linear `g` with transverse conditioned agreement
   at least `2^{-2(1-1000ρ²)h}/5`. The current `8S` mass bound is only its
   input. `ActualChangedAmbient8SBoundary.first_inverse_witness_of_eightS`
   assumes an all-ambient inverse and returns only one zoom, so it does not
   establish this robust theorem. Preserve arbitrary fixed legal tables and
   the explicit representative-class collision charge.
2. Compose that decoder, threshold ladder, maximal counting, covering,
   vector-law correction and random extensions into a decoded outer strategy
   with success `≥2^{-10h²}`, then use the fixed-gap outer contract and the
   proved factor-two strict inequality to establish PCP NO soundness
   `≤R^{-(1-ξ)m}`. This must hold for every legal NO outer instance and all
   tables, with `κ` independent of later `ε₁`.
3. Build the positive-error outer reduction after fixing `m,h,J,β` for
   every fixed positive `τ`; account for legitimate-tuple padding and all
   `m+1` original/clique-resampled blocks in YES. The numerical `τ/75`
   bound is proved, but the sampled game/PCP instance and its encoded
   polynomial-time map are not.
4. Apply the scoped HN compilation, then prove manuscript-new AND product,
   dyadic sampler approximation, finite empirical list with simultaneous
   YES/NO control, exception repair to exact YES satisfaction, rational
   weight rounding with a polynomial common denominator, and encoded FP
   implementation. Preserve the strict NO threshold and fixed-`L` runtime.
5. Prove that the seven externally supplied cutoff functions in the
   ledger-selected family are sufficient for their exact source and
   manuscript inequalities, and use that family throughout the actual
   reduction in place of the `n+2` production placeholder. Then connect the concrete SAT-to-outer and outer-to-CMMSA
   `SeededMap` stages to `cmmsaPromise` and apply `ActualTheorem1`.

Theorem 1 remains conditional until these obligations are Lean theorems with
the cited inputs represented as explicit external parameters. Numeric
parameter progress alone has not reduced the unproved NO-soundness gap.

## Three-lens review status

| Lens | Status | Scope of conclusion |
| --- | --- | --- |
| Proof-adversarial | **NO-GO for core; GO-WITH-NOTES for narrow arithmetic** | The numerical lemmas are Lean checked. The changed-ambient decoder and the encoded YES/NO construction are absent, so Theorem 1 cannot close. |
| Complexity theory | **GO-WITH-NOTES for bounded arithmetic; NO-GO for completed core** | The revised review accepts arbitrary positive real `κ`, an integer `A` chosen afterward, and the conditioned exponent comparison. It does not validate the missing decoder-to-outer strategy or encoded reduction. |
| Non-claims boundary | **GO-WITH-NOTES** | The module and ledger identify cited contracts as external and the core certificate as incomplete. No unconditional manuscript certification is claimed. |

The review table is a status record, not a route-final three-lens closeout.
Planning review-debt story **S3126** blocks any route-final or core-certified
claim until the missing force chain, encoded YES/NO construction, and faithful
contract interfaces are proved and reviewed.

### Late-τ YES bounded composition

`ActualLateTauYesComposition` proves the `m+1` block union and legitimate-event
conditioning bound `≤τ/75` on a finite law. Its exact per-block premise is
`μ(legitimate ∩ badᵢ) ≤ J ε₁`; the conclusion concerns the probability that
all blocks are good, not the actual PCP accepts event. The Checks target built
green (3234 jobs), reporting only standard Lean axioms. The bounded three-lens
review is recorded in `docs/late-tau-yes-composition-review-2026-09-29.md`:
GO-WITH-NOTES for this composition and INCOMPLETE for core Theorem 1.
Remaining YES interfaces are the external positive-error SAT-to-outer map
after the fixed NO parameters, disjoint-copy padding with
`a≤min(τ/100,1/4)`, joint numerator bounds for the original and all
clique-resampled blocks, and containment of the all-good-block event in
actual honest PCP acceptance. This changes no numeric NO-soundness bound.

`ActualHonestTaggedTransport.honestOriginalAccepts_of_goodU` now proves the
pointwise acceptance implication for the actual post-padding copied verifier:
for every fixed occurrence instance, copy count, `J,t,h,k`, arbitrary ambient
linear assignment `f`, and every `OriginalDraw x`, if `f` satisfies every
copied equation in `x.U.rows`, the single globally legal predraw
`honestOriginalAssignment I copies f` accepts `x`. The proof uses a good
presentation per quotient class when available, valid fallback elsewhere,
and tagged three-way transport coherence. It imposes **no goodness premise on
sampled class representatives**. Checks passed (3262 jobs), with only standard
Lean axioms. All three lenses are GO-WITH-NOTES for this bounded pointwise
result and NO-GO for the PCP/core certificate; see
`docs/honest-class-table-good-u-bridge-2026-09-29.md`. The same fixed table
can be tested on each original or clique-resampled block, but a Lean joint
`m+1` experiment, its actual per-block conditioned marginal bounds, and the
transport of the outer honest assignment to this tagged functional remain
missing. The numeric NO-soundness gap is unchanged.

### Fixed-U contract bounded review

`lake build PvNP.RealizableHardness.ActualMZFixedUSourceDecoderContract`
passed (3260 jobs); the separate checks target records `#check` and
`#print axioms` for its `decode` projection. Three post-fix lenses judged the
**bounded external contract GO-WITH-NOTES**: proof adversarial, complexity
theory, and non-claims. All three retain **NO-GO for the changed-ambient
`8S`/core Theorem 1 claim**. The remaining source-tagged alignment obligation
above and planning review debt S3126 remain open. This increment reduces no
numeric NO-soundness gap.

### Late-τ actual copied-row conditioning budget

`ActualLateTauPadding.exists_late_tau_padding` is Lean checked for every
fixed actual occurrence-allocation instance with `m>0`, every fixed `J`, and
every later rational `τ>0`. It selects a fixed `T≥4` and
`copies=actualPaddingCopies J T`, and proves for the uniform ordered copied-row
draw that its actual illegitimate `GoodOrderedQuestion` complement mass
`a≤τ/100`, `a≤1/4`, and legitimate mass is exactly `1−a`. This discharges the
copied-question **conditioning budget** used in manuscript §7. The Checks
target built green (3388 jobs) with only standard Lean axioms. Three lenses
were GO-WITH-NOTES for this bounded padding statement and NO-GO for Equation
(21) / core Theorem 1; see
`docs/late-tau-tagged-padding-boundary-2026-09-29.md`.

The MZ positive-error outer YES / encoded bounded-occurrence 3-Lin hardness
result remains a visibly external source contract. The original-question
marginal is now proved for the declared post-padding draw law, as recorded
below. All `m+1` clique-resampled block
joint failure bounds remain unproved; so does the implication from all-good
blocks to actual honest acceptance. `taggedCopy_value` proves source optimum
preservation separately, but typed degree preservation and an encoded
polynomial-time copy constructor remain open. This result does not reduce the
numeric NO-soundness gap.

### Original ordered padding to declared post-padding U marginal

`ActualOriginalOrderedPaddingLaw` proves, for every fixed actual occurrence
instance `I`, copies, and `J` with a nonempty raw ordered-row type, that the
raw uniform legitimate event has mass exactly `actualTaggedGoodMass I copies J`.
With `0 < copies` and `0 < m`, this is `1 - actualTaggedBadMass I copies J`.
For a nonempty `TaggedGoodU` type, conditioning the raw eligible ordered tuple
and forgetting its order gives uniform `TaggedGoodU` mass. For each fixed
`I`, copies, `J,t,h,k`, assuming every sampled tagged center and leaf fibre
is nonempty, the declared `originalLawFromTagged` draw has uniform `OriginalU`
marginal, and `conditional_raw_eq_originalDraw_U` equates that marginal
pointwise with the conditioned raw ordered law. These marginal theorems hold
at each fixed copy count; the earlier `exists_late_tau_padding` chooses an
admissible count after the later positive tau choice, with bad mass at most
tau/100 and 1/4.

The Checks target built green (3437 jobs); its eight principal declarations
show only standard Lean axioms under `#print axioms`. The proof adversarial,
complexity, and non-claims lenses each gave GO-WITH-NOTES for this bounded
U-marginal identity and NO-GO for Equation (21) or the core Theorem 1
certificate. See `docs/original-ordered-padding-u-marginal-2026-09-29.md`.
This result identifies the U marginal of the declared post-padding draw law.
It does not prove the resampled block U laws or their joint equation-failure
bounds, the actual all-good-block acceptance implication, or any new NO
decoder estimate. The numeric NO-soundness gap is unchanged.

### Later combined source-conditional YES certificate

The entries above record their earlier bounded states. The later
`ActualCommonBlockYesComposition` proves the actual common declared draw's
`m+1` equation-block union bound and the fixed legal honest table's rejection
bound `≤τ/75`, conditional on a copied positive-error assignment. The later
`ActualOuterEncodedOccurrenceYesBridge.external_yes_combined_eq21` discharges
that assignment and all selected-padding geometric fibre hypotheses **from
one fixed external `ExternalMZOuterSource` inhabitant**. For fixed `blocks,J,t,h`
with `J>0`, `t≤2h`, `h≤J`, each 3SAT YES input and each later `τ>0`, it
selects `ε>0`, encoded output `E`, actual `T≥4`, and one fixed predraw `f`.
It proves `ε<1-s`, `ε≤τ/[100(blocks+1)J]`, collision mass at most `τ/100`
and `1/4`, the concrete `PositiveErrorAssignment`, and declared-draw honest
rejection at most `τ/75`. `padded_draw_fibres` proves raw, eligible,
presented, center and leaf nonemptiness using the existing dimension
constructions. Checks built green (3491 jobs), with only standard Lean axioms.
See `docs/outer-encoded-occurrence-yes-bridge-2026-09-29.md` for exact
quantifiers and the separate initial bounded three-lens review. Review of
this **combined** increment is pending.

This is a conditional YES result, not a new inhabitant of the MZ external
contract. The fixed encoding/parser computational implementation and
fixed-`L` encoded runtime for the full reduction remain open. The source
product-game observation bridge, decoder, and full NO soundness also remain
open. Core Theorem 1 is **INCOMPLETE** and its NO gap is unchanged.

### Classical analytic subcontracts and core-first phase boundary

The six entries above remain the historical top-level source inventory.
The conditional core route also needs explicit classical analytic
subcontracts from [MZ v1, Section 4.2, Theorem 4.6 and Lemma 4.7](https://arxiv.org/pdf/2510.23991v1).
Their exact Lean interfaces have not yet been added or verified. This
classification is a planning decision, not an imported theorem or a new
proof of an analytic estimate.

The hypercontractive subcontract must use the existing
`BinaryMatrixFourier.PseudorandomExact`, Boolean indicator, rank projection
and normalized `lpNorm`: for the source-checked matrix shapes with even leaf
width, nominal restriction budget `r`, positive rank `i <= r`, and dyadic
`p >= 4`, with nonnegative `delta` and no added `delta <= 1` premise,
its conclusion is
`lpNorm p (rankProjection i (indicator f)) <= 2^(500*i^2*p) * delta^(1-2/p)`.
Dependent or zero restriction equations and zero dimensions remain within
the typed domain. No basis-invariance or full-rank-conditioning premise
belongs to this hypercontractive field. The nominal-to-source restriction
alignment remains an explicit obligation.

The fresh primary-source conditions audit in
`docs/mz-classical-analytic-contract-conditions-2026-09-29.md` supersedes the
earlier proposed delta<=1 guard and unrestricted-width wording. It is a
source-condition assessment, not an inhabited Lean contract.

The spectral subcontract must separately preserve Lemma 4.7's exact
operators, normalized averages, source applicability and basis-invariance
premise. It must not be identified with the manuscript's stronger
finite-character lemma without a proof of that comparison. In particular,
typing an operator bound does not establish its use for the actual
common-center experiment.

Source-checked classical fields may be explicit parameters of the
conditional core. Their inhabitants, including the A18/A21/A22 engine and
the cited spectral proof, are deferred to the outward certification phase
after that core closes. The manuscript-new actual matrix-lift, moment,
inverse, robust `8S`, parameter and source-law comparisons must still be
proved from those exact fields. No field may assume the final actual moment
upper bound, `AllAmbientInverse`, robust decoder, NO soundness, or encoded
core conclusion. Standalone contract typing does not count as progress on
those force obligations. Full manuscript certification still requires
discharging all classical contracts and reproducible consolidation.

### Actual fixed-functional star law alignment (2026-09-29)

The bounded increment in `ActualFixedFunctionalStarMoment.lean` proves
`matchingStarMass_cast_eq_grassmannExperiment`: the real cast of the
existing actual ordinary-star matching mass equals the existing
`MatrixGrassmannIdentity.grassmannExperiment`, for the same fixed
functional and predraw center and leaf tables. Its only dimension premise
is `c + s <= finrank V`. The event retains the center condition and every
ordered leaf condition, including the center at `k = 0`. The proof uses
the actual star-law atom, exact rational-to-real casts and finite
cardinality normalization; `Above R s` and `Extension R (c+s)` are the
same carrier. No rank-conditioned or independently redrawn center is
substituted.

Frozen raw SHA-256 pins:

- Main: `202014CFC75A05EC63FE4F55B9637B7B84705B78BA68EA886AA384072DA31893`.
- Checks: `B92F0742670201CC2988B28EDE0F55E113889E475101D6291DB0E21361AD2E70`.

Direct cached Lean 4.34.0-rc2, one thread and the captured project
`LEAN_PATH`, returned exit 0 for main session `66545` (receipt chunk
`c2371e`) and focused Checks session `77356` (chunk `f5561f`). Both normal
project oleans were exported. Checks printed all three export signatures
and only `[propext, Classical.choice, Quot.sound]`, and compiled the
zero-leaf center-retention example. Earlier diagnostics and controlled
resource stops are not counted as successful checks.

| Top-level lens | Verdict | Evidence and limits |
| --- | --- | --- |
| Proof-adversarial (root) | GO-WITH-NOTES | Independently read and rehashed the frozen pair; checked actual atoms, casts, ordered-tuple normalization and focused export/axiom receipts. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Same fixed tables and functional precede the shared-center experiment; no distribution or quantifier weakening. Orchestration and localized proof-hint overlap is disclosed; this is not an independent proof-author check. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | Language states only the exact Grassmann experiment identity; no analytic, inverse, runtime, NO or core conclusion. Final verdict follows whole Checks exit 0. |

All three verdicts apply only to this frozen pair and the bounded scope
above. Review and proof debt for earlier increments is not discharged by
this table.

This is an exact finite-law identity. Coordinate-array/BinaryMatrix
transport, the appended-column operator, the actual matrix moment bound,
inverse theorem, robust `8S`, encoded NO soundness and the conditional
core remain open. Unverified complement-consumer and manuscript-margin
drafts are outside this accepted scope. Classical-contract discharge and
full manuscript consolidation also remain outstanding.

### Actual binary-matrix moment transport (2026-09-29)

`ActualFixedFunctionalBinaryMatrixMoment.lean` proves a coordinate-column
transpose equivalence, the exact unconditional binary-matrix mean for
`rawTF`, and `matrixMoment_eq_actualBinaryMatrixMoment`. The actual moment
has one uniform shared base matrix, with the unconditional extension mean
raised to the ordered-leaf count. The accepted `rawF` and `rawG` retain
their zero values on deficient arrays. No sampling distribution is
conditioned on rank.

`matchingStarMass_cast_le_twice_actualBinaryMatrixMoment` consumes the
accepted actual star-law identity and `grassmann_le_twice_moment`, for the
same fixed functional and predraw tables. Its dimension premise `hdV`,
positive total width `hD`, and explicit numeric rank-loss premise `hsmall`
are retained. The selected-parameter proof of `hsmall` is not supplied by
this increment.

Frozen raw SHA-256 pins:

- Main: `87CC5C417FD419E4E475DB66C209E5A8A6DA1EDE258BFA0D3532950398DA9B45`.
- Checks: `5419EE6CA664BA8E2DE55C0CC3BC4AA02E6554B868F86BA6A7257417FC7790AB`.

Direct cached Lean 4.34.0-rc2 with one thread returned exit 0 for main
session `5243` (chunk `e02a95`, empty diagnostics) and focused Checks
session `10350` (chunk `538247`). Both normal project oleans were exported.
The reconstructed `LEAN_PATH` used this satellite's root build library
and extant local package build libraries: aesop, batteries, complexitylib,
importGraph, LeanSearchClient, mathlib, plausible, proofwidgets and Qq.
It is not asserted to be identical to the previous captured path.
Checks confirmed all four exported objects. The coordinate equivalence has
exact axiom profile `[propext, Quot.sound]`; the other three exports have
`[propext, Classical.choice, Quot.sound]`.

Emitted olean SHA-256 pins, independently reverified by the root reviewer:

- Main: `BD889BE1237ED64D14B22E6F8C6350B81EB6B168053B2085E2DBFB5229F59AC2`.
- Checks: `0BF79924A15753E4F03DE71FE75835AD79D3BED89E2B108A5185E7B291563A91`.

| Top-level lens | Verdict | Bounded review scope |
| --- | --- | --- |
| Proof-adversarial (root) | GO-WITH-NOTES | Independently read frozen source and Checks, rehashed source/objects, and verified exact coordinate sums and consumption of the accepted law and finite rank-loss comparison. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Unconditional append draws, shared base matrix, fixed functional/tables and exact normalizers are retained. Orchestration and localized proof-hint overlap is disclosed; this is not an independent proof-author check. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | The explicit `hdV`, `hD` and `hsmall` premises and missing operator/analytic applications remain visible. Final verdict follows whole Checks exit 0. |

The actual single appended matrix indexed by `Fin (c+s)`, its existing
`rankImageBoolean` lift, basis invariance and the cited analytic operator
application remain open. This transport does not prove the analytic moment
bound, inverse theorem, robust `8S`, NO soundness or conditional core.

### Accepted actual append-column rank-image operator alignment (2026-09-29)

`ActualFixedFunctionalAppendOperator` proves the all-array coordinate span and
injectivity bridges, the existing rank-image Boolean lifts of `rawG` and
`rawF` (deficient arrays contribute zero), and the unconditional append-column
mean. Its shared-center kth-moment identity consumes the accepted binary
matrix transport. The actual matching-star mass bound retains the same fixed
functional and predrawn tables and the explicit `hdV`, `hD`, `hsmall` premises.
The center factor remains present at k=0.

Frozen source SHA256:
- Main: `EB71A55A38E8922333058F0D05D8E48472003AAA9BEE2B9F01A9DE00668A7B77`.
- Checks: `6995A25BBEC41EA6C1ECE710CA11EA2DFC9585B5106E97C416A4DD4909BF5E9A`.
Normal cached object SHA256:
- Main: `5E37F434B0B0F20E3AE5F3895D6129D2432EEDEAC033B88D776DBB1043981828`.
- Checks: `8E662C6F9EF73DFA46E77DF80CE91774E4AC381C46525D60C9C91A8A2A745312`.

Main author build session 63464 reported exit 0. Author session 61615's
manually transcribed output was disqualified after a namespace mismatch;
it is not authoritative raw evidence. Acceptance uses the necessary Sol
machine audit session 5855, native Lean PID 25088, structured terminal chunk
3b1aab: exit 0, empty stderr, nine actual `PvNP.RealizableHardness` signatures
and five material export profiles containing only
`[propext, Classical.choice, Quot.sound]`. The audit imported the frozen normal
main object and automatically persisted stdout, stderr, native exit and pins
in [the machine receipt](append-operator-machine-checks-audit-2026-09-29.json),
SHA256 `5D3DD371D6EE18E5ABE6236884206C7E5A03E48A54363A1D06944DDCE20A9EEC`.
Root independently read and hashed that receipt and the frozen artifacts.
Fresh free-memory samples reached a minimum of 1,936,468 KiB, above the
1,572,864 KiB owned-process stop guard; no controlled stop occurred. The
receipt's cached WorkingSetBytes values are not evidence of peak memory.
These resource limits are agent operating policy, not manuscript premises.

| Top-level lens | Final verdict | Scope and evidence |
| --- | --- | --- |
| Proof-adversarial (root) | GO-WITH-NOTES | Independently read the all-rank source and Checks, verified frozen objects, and restored the verdict after reading the authentic machine receipt. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Fixed functional/tables, unconditional appended draws, shared center, deficient-zero lift and exact normalizers are retained. Orchestration and proof-hint overlap is disclosed; this is not an independent proof-author check. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | Independently read and hashed the source, Checks and authentic receipt; bounded operator/moment alignment wording is accurate. |

All three final verdicts were restored after the receipt issue was resolved.
This bounded increment does not discharge inherited S3126/full-manuscript
review debt. Selected-parameter `hsmall`, all-matrix basis invariance, the
classical HC/spectral application, actual analytic moment estimate, inverse,
robust `8S`, numeric NO and conditional/full core certification remain OPEN.
Consumer/margin drafts remain unverified. Classical contract inhabitants are
still deferred outward until the conditional core closes.

### Actual rank-image right-basis invariance (2026-09-29)

`ActualRankImageRightBasisInvariance` proves range and injectivity preservation
under right multiplication by U with an explicitly supplied two-sided inverse V,
for every matrix M. The existing `rankImageBoolean` and its indicator are
therefore invariant, including deficient matrices. Actual fixed C, T and f
specializations consume this result in the accepted leaf append average and
shared-center kth moment. These are equalities after precomposing the leaf
FUNCTION by X -> X*U; they do not assert invariance of the conditional sampler
under a transformation of the base matrix or arbitrary block mixing. All draws
and normalizers are unchanged, and k=0 retains the center factor.

Frozen source SHA256:
- Main: `F2286607C739FF54B221DD209A4148BF0FC4915DEB4A956ACE72D8EE49986957`.
- Checks: `33D4375176C750FB73BA422DAAF3E1FE84A36DFA92E93185DDE6CD057EA0FD0E`.
Normal object SHA256:
- Main: `883E9836F567EF4CDA088F2DB466B7A0905101A7F85F7BA22DC1977A59CC5320`.
- Checks: `48FF70D7143C2BA17427CDD009697FF8D01577132A4D28F36FBE6E601E270EE5`.

Author direct-j1 main session 34284 and Checks session 57326 both have
authenticated automatic native exit 0 receipts. Main stdout contains only four
deprecated dif_pos/dif_neg warnings. Checks prints seven exact signatures and
four material axiom profiles, each `[propext, Classical.choice, Quot.sound]`.
Root and Sol independently read and hashed the machine evidence and frozen
artifacts; no manually reconstructed stdout is used.
- [Main receipt](ActualRankImageRightBasisInvariance-main-receipt-20260930T001939092Z.json), original raw SHA256 `02246AF81DA1D2D9B77657C29F2CCC90E9E308F8521CCDAD888E53E39EFBC8F3`.
- [Checks receipt](ActualRankImageRightBasisInvariance-checks-receipt-20260930T002117029Z.json), original raw SHA256 `E525161E4F4D558A39F02B3ACC0462A8F2C71A9F62716EF621F5569947E61DF8`.
Minimum fresh free-memory samples were 1,975,728 and 2,231,108 KiB respectively,
above the agent operating stop guard 1,572,864 KiB. Neither run was stopped.

| Top-level lens | Verdict | Scope |
| --- | --- | --- |
| Proof-adversarial (root) | GO-WITH-NOTES | All-matrix inverse transport, full and deficient lift branches, actual means and k=0; authenticated main/Checks and normal objects verified. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Same fixed f/C/T, unconditional append draws and shared center; input precomposition is not sampler invariance. Orchestration and proof-hint overlap is disclosed; this is not an independent proof-author check. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | Independently read and hashed the authenticated Checks receipt, seven signatures and four standard profiles; no unproved analytic or sampler-invariance claim. |

Basis invariance of these concrete lifts is now kernel checked. Exact classical
HC/spectral application, selected hsmall, leaf-label/failed-zoom alignment,
analytic moment bound, actual inverse, robust 8S, numeric NO and conditional/full
core remain OPEN. This increment does not discharge inherited S3126 independent
review debt or the outward classical source-contract inhabitants.

### Actual leaf-label and failed-zoom rank-image alignment (2026-09-29)

`ActualLeafLabelRankImageAlignment` proves that the actual linear-map matching
bit and the existing pointwise `matchingLeafSet` use precisely the same T and f.
Their full Grassmannian predicates, existing rank-image Booleans (including
deficient matrices), and indicators agree. The consumer transfers the existing
failed-zoom finite nominal-restriction comparison onto this actual leaf lift:
`PseudorandomExact r (2 * (e : Real))`. It retains r<d, e>=0, ALL q/Q/DecodedPair
quantifiers, exact q+codim=r, nonempty Zoom and agreement<=e. No row-validity
premise is introduced. This supplies pseudorandomness, not a hypercontractive
estimate or an inverse conclusion.

Frozen source SHA256:
- Main: `5991FC3DDC2AFE577C6E4F77CF68707B05BC1F233107C1E48DC840B7FB9080C2`.
- Checks: `ED3EE6B63AC02B1133A5FCD2696C325A3198BD98044051515AA7EACC072745FA`.
Normal object SHA256:
- Main: `4CB525619006C19B30B54D494E5D196D8C3155AEF229BB90B724170467AEB952`.
- Checks: `D11EF6B152C6FA17A813F762F6248D468FFFCD25AFBE52C33A3AF72B78AF5FC4`.

Main session 92104 has native exit 0 and empty stdout/stderr. Checks session
7577 has native exit 0, five exact signatures and three material axiom profiles,
each `[propext, Classical.choice, Quot.sound]`. Its PowerShell wrapper exited 1
AFTER persisting the authentic receipt, during summary formatting; that is not
a Lean failure. The original main receipt was found at its exact Temp subfolder
and copied byte-for-byte, without reconstruction. Authoritative raw receipts:
- [Main](ActualLeafLabelRankImageAlignment-main-receipt-20260930T003000347Z.json), SHA256 `9863C216AAD2A93983766BA720A2DCFE4F58064D7C4797076ACBE9BD40870B45`.
- [Checks](ActualLeafLabelRankImageAlignmentChecks-receipt-20260930T003254303Z.json), SHA256 `DA0B3AB6B9510095665EB10671D37A1FD7FE3BB497BB39C9A614A88072D64B35`.
Fresh free-memory minima were 2,076,240 and 1,925,348 KiB; no controlled stop.

| Top-level lens | Verdict | Bounded scope |
| --- | --- | --- |
| Proof-adversarial (root) | GO-WITH-NOTES | Independently verified frozen source/objects and authenticated receipts; all failed-zoom quantifiers and nominal budget are retained. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Same T/f, matrix lift, complete failed-zoom quantifiers and exact delta=2e. Orchestration and proof-hint overlap is disclosed; this is not an independent proof-author check. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | Independently verified the actual Checks receipt and five signatures/three standard profiles; distinguishes native Lean success from wrapper summary failure. |

Intended failed-zoom invocation, derivation of 2e<=1 if downstream arithmetic needs it,
exact HC/spectral application, selected hsmall, analytic moment bound, actual
inverse, robust 8S, numeric NO and conditional/full core remain OPEN. Inherited
S3126 review debt and outward classical contract inhabitants remain open.

The standing-assumption/application audit
`docs/mz-standing-assumptions-application-audit-2026-09-29.md` identifies the
actual complement dimensions n=2J, c=t and s=2h-t, hence even leaf width 2h.
Selected-parameter specialization remains open. Before the coordinate moment
theorems can serve the actual complement caller, prove A -> CoordinateAmbient(2J)
linear-equivalence transport of the SAME C/T/f and the uniform Grassmannian laws;
the finrank equality alone does not supply that bridge. Source-scoped classical
clauses must retain their checked standing assumptions. This audit is not a
classical contract inhabitant or an actual analytic moment bound.

### Actual post-append Fourier cross-level orthogonality (2026-09-29)

`ActualAppendFourierCrossLevelOrthogonality` proves the exact unconditional
append operator has zero averaged product between two distinct Fourier ranks
of the SAME fixed real function F. All base and append matrices are included;
there is no full-rank conditioning or basis-invariance premise. Append averaging
kills nonzero tail frequencies. For surviving tails, distinct full ranks imply
distinct base frequencies, so character orthogonality and finite coefficient
expansion prove the final post-operator identity. The helper
`appendAverage_character_mul_eq_zero` specifically assumes distinct RANKS,
although its descriptive comment refers to distinct frequencies. Zero dimensions
are included. This is an internally proved finite identity, not a claim that the
paper states arbitrary-function spectral estimates.

Frozen SHA256 pins:

- Main source: `AE8D620F887E45B9B4445375640E5EB3AE54C5B56A81186DF77B6FC55D741652`.
- Checks source: `26652622F88D67216BA355F14D240211D95EE828DCBBF18244457D08755894A4`.
- Normal main object: `46A207E2AD408BF376617BD8D3702955AFC32EEC392D70C69333DA4AC86C8BF9`.
- Normal Checks object: `2FCD60504BE5CA64DA2DC7C031A63A9D7219323CB2DAC39F94C1912B10D7AF08`.

Authoritative machine evidence is preserved byte-for-byte under
`docs/native-receipts/ActualAppendFourierCrossLevelOrthogonality/`, including
the Python capture helper, native 0/7 self-tests, JSON receipts and raw streams.
The helper SHA256 is `1548CA444C2EF3A12F5736A1B2CC3C81849EE299DA79DBA614A92D0E4B3F2629`.
Original paths are retained in each receipt. Main session 34972 and Checks
session 89834 both have actual Python Popen native exit 0, success=true,
unchanged source pins, fresh normal objects, and guard_terminated=false.
Main stdout/stderr are empty. Checks has eight exact signatures and three
material profiles `[propext, Classical.choice, Quot.sound]`; the final theorem's
profile covers all its transitive helper dependencies and excludes sorryAx.

- Main JSON `cmmsa_native_lean_20260930T012553Z_e70997610da24ce8ba871774606c88d4.json`: raw SHA256 `EE6347DA5954F7EB7BABDE4CEA5E246729BB1625EF4D0A5D2C121511C6933C0C`.
- Checks JSON `cmmsa_native_lean_20260930T012717Z_10181d86d5984b578478c85a93264745.json`: raw SHA256 `5F579571F9270087F6FC20594AD1D2C456950C503CD644403ECCB029E69BFAAE`.
- Checks stdout: `1C7C6CF2F30FADC8686409B32FA134961EAF9C9D90ABD5764A78400742EA6576`.

Earlier sessions 30001 and 93047 are NOT acceptance evidence: their capture
reported null or inconsistent zero exit while Lean errors remained, and omitted
normal -o output. The new Python capture and successful reruns supersede those
disqualified receipts; they do not retroactively validate them.

| Top-level lens | Verdict | Bounded scope |
| --- | --- | --- |
| Proof-adversarial (independent reviewer) | GO | Full frozen source, actual native receipts, normal objects and focused Checks inspected. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Same F, unconditional append draws, common base and exact finite weights; no spectral magnitude or runtime assertion. Orchestration and proof-hint overlap is disclosed; no direct proof edit was performed. |
| Non-claims boundary (separate reviewer) | GO-WITH-NOTES | Independently verified frozen source, durable successful receipts and raw standard profiles; the arbitrary-function result is local, not claimed verbatim from MZ. |

Exact complement-to-coordinate SAME C/T/f star mass AND center mass transport,
selected parameter guards, source-scoped HC/spectral application, analytic moment
bound, actual inverse, robust 8S, numeric NO, conditional/full core and final
consolidation remain OPEN. S3126 review debt and outward classical contract
inhabitants remain open. This increment supplies post-append orthogonality only.
Task/OpenCode fallback governance debt is unchanged. Byte-exact working evidence
hashes above are retained even if Git text normalization changes committed hashes.
Git-normalized LF receipt SHA256 values are main
`DB84473E94AEB438F50354151204E42EE93FFA41596E41A33F979CDBC5598350`
and Checks `3B9C0C8B5E20D309FE41AF6E1010598A47E5034263079A11A7F24B372B7CC65B`.
The disqualified JSON originals are preserved with explicit `DISQUALIFIED-`
filenames in the same evidence directory; their diagnostics remain historical,
not acceptance receipts.

### WIP: actual complement-coordinate mass transport (2026-09-29)

This is an UNVERIFIED source checkpoint, not an accepted theorem increment.
`ActualComplementCoordinateMassBridge` now contains the full attempted
`matchingStarMass_actual_coordinate` and `matchingCenterMass_actual_coordinate`
proofs. Both retain the SAME actual A, original tagged C/T, chosen f, and t/d/k
ordered uniform star law. Selected coordinate tables explicitly consume tracked
`transportedCenterTable`/`transportedLeafTable`; f is composed with the inverse
actual basis coordinate equivalence. Exact pushforward/event preimage proofs are
attempted, without a final-mass hypothesis. The redundant hdCoord proof remains
explicit and must be derived from the actual hdA guard at the final caller.

Stable WIP source SHA256:
`290767FB56C04CBA4FB1BC8BE6F1900AB6F2AC0E7070F1BC3E62F84245D593DD`.
This latest repair has NOT been checked. The last checked source was
`CC6CA78901CA068998978CB62E74BA9278460B9F4C7D133FCE014EC207ABD897`:
native exit 1, guard_terminated=false, no fresh accepted object. Its diagnostics
were inverse extension containment and stale named m after renaming leaf count
k. The current source rewrites the mapped-back center with Grass left_inv and
uses the actual k parameter. Earlier diagnostics included mapped finrank,
namespace/arity and dependent Sigma inverse proofs; the latter were replaced
by accepted Equiv.sigmaCongr/piCongrRight APIs. Lean's failed-elaboration sorry
warnings are NOT a standard axiom receipt or accepted proof.

Coordinate history is separated from accepted POST evidence in
`docs/native-receipts/ActualComplementCoordinateMassBridge/`. It preserves two
prelaunch refusal triplets and seven authentic native-failure triplets, with
original paths/arguments/pins in machine JSON and raw stdout/stderr retained.
Latest native JSON `cmmsa_native_lean_20260930T015939Z_364ca420c0e94f389a6059d8a4a6784c.json`
has raw SHA256 `555945E445C32ACD703FB3503AD0612DECD361C6710110689ED984CA199174E5`;
its stdout SHA256 is `FEB9C09D50279D53DAA23470D195B1FE7EFBD22BE64C01B2ED4680975D23674F`.
All coordinate launches used the inspected Python capture after the two explicit
prelaunch path errors. No failure was attributed to a crossed memory guard.

Both exact mass proofs, final source/Checks green, no-sorryAx profiles and the
three final review lenses are STILL REQUIRED. No coordinate bridge acceptance,
analytic moment estimate, inverse, robust 8S, numerical NO or conditional/full
core closure is recorded. This WIP checkpoint preserves progress for continued
Luna proof work and does not replace the full bridge target with carriers.
The stable source has the same working and Git blob SHA256. Git-normalized
latest diagnostic JSON SHA256 is
`C299E53BD7B7F5B0EF90EF80FAC2218B2DAB62A7CCE74040F41E5F95F65C2740`;
the raw byte hash above remains the machine receipt's original pin.

### Actual complement-coordinate star and center mass bridge: accepted bounded increment

The WIP checkpoint above is historical. The frozen final module now proves
`matchingStarMass_actual_coordinate` AND `matchingCenterMass_actual_coordinate`
for the same chosen actual side complement A and original tagged C/T and f.
The source tables are the tracked transportedCenterTable/transportedLeafTable;
coordinate labels compose with the induced restricted inverse, and the same
functional composes with the actual coordinate inverse. The ambient has 2J
coordinates by sideComplement_finrank. Grass/extension equivalences preserve
containment, and sigma/pi equivalences retain one shared center with all ordered
leaves. Uniform-law pushforward and exact matching-event preimages give BOTH
Rat mass identities under the SAME t/d/m joint law, including m=0 center beta.
The coordinate dimension proof is derived by actualCoordinateDimensionBound
from hdA; no independent coordinate guard, matching-mass premise or proxy labels
are added. The basis choice is noncomputable proof transport, not a runtime
algorithm claim.

Frozen source SHA256: main
`0BDD2A95493E631DAF013FB4915B985A67B45FC137CD2A6DA22B1C24BFDE5857`;
Checks `A7803212758A4EC49F64E34D09165B7D5CB6CF57CB88B53FEB5E12AF0E252D5B`.
Normal object SHA256: main
`E29A8D66125F0B3F33B0497B7CBC26B65033A762A530A2849ED1D4B95AA91FA8`;
Checks `BFC5525D84ECA1CC9E8AE217E7B2FE72512E3DC9A8584F9FFCB3F7FB4B2CF134`.

Main session31098 and Checks58218 have genuine native exit0, success=true,
unchanged source pins, fresh normal objects, guard_terminated=false and empty
stderr. Main stdout contains six letI-style warnings only. Checks supplies four
exact signatures and four standard-only profiles
`[propext, Classical.choice, Quot.sound]`, excluding sorryAx transitively.
Raw machine triplets are byte-preserved in the coordinate evidence directory:

- Main `cmmsa_native_lean_20260930T023115Z_8b90c4a4a2204666b1cbc029e0f5a02a.json`, SHA256 `99833B5C37855AECCA79C9FAC97F33990FB0A169F3009DAB2BC5E47B4C3F3D4C`.
- Checks `cmmsa_native_lean_20260930T023253Z_1ac92978f4e340a4a6ce65d134ca607d.json`, SHA256 `5A741C815164984301BB885DA12DC59A47683C90C24F1B65207532A865E54466`.
- Checks raw stdout SHA256 `2F337C63CB8713261543E4D33A9309BC48D80BCEDB97A3A502633EBEEAD15294`.

The preceding authentic failures are diagnostic history, not acceptance receipts.
Finite-instance/namespace and dependent event proofs were repaired without
premise changes. The center theorem uses scoped maxHeartbeats400000 after
actual whnf timeout; the runtime memory guard is unchanged. Predicate congrArg
transport replaced repeated dependent simplification. A mistyped expected SHA
was refused before native launch and remains separate nonnative history.

| Top-level lens | Verdict | Bounded scope |
| --- | --- | --- |
| Proof-adversarial (independent reviewer) | GO-WITH-NOTES | Independently hashed source, receipts, outputs and objects; no vacuity or hypothesis drift. Actual A/U/htd/hdA remain supplied. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Same fixed C/T/f, exact joint law and both Rat masses, no conditioning or runtime claim. Orchestration and extensive proof-hint overlap disclosed; no direct proof edit by Sol. |
| Non-claims boundary (independent reviewer) | GO-WITH-NOTES | Exact law and both Rat identities with same C/T/f; no existence, positivity, selected-parameter, analytic or core claim. |

Selected parameter and hsmall application, actual classical HC/spectral moment
application, inverse, robust8S, numerical NO, runtime, conditional/full core and
final consolidation remain OPEN. Source-contract inhabitants remain outward
obligations after conditional-core closure; review fallback governance debt and
S3126 review debt persist. These exact mass identities do not supply an analytic
upper bound or close the core. All three final lenses permit this bounded increment.
The exports do not prove existence of A or U, positive matching mass, or actual
selected leaf-parameter guards. The preceding route/audit documents are historical
planning evidence, not acceptance of those remaining caller obligations.
Git-normalized LF final receipt SHA256 values are main
`AC0AA7380C82C1C12092E80CCD216C744FECD475E72A0CFC1121BC33C0D51796`
and Checks `2B72873DDE2561D128606625B8C8BA997737538EFB61B5F139C17959056FA72E`.
Raw working copies remain byte-exact to the original machine streams and receipt
hashes above. Source working/blob pins are identical.

## Selected actual complement mass-to-moment comparison: accepted bounded increment

The frozen new module `ActualSelectedComplementAppendMoment.lean` has native
Main and focused Checks green. All three final top-level lenses permit this
bounded mass-to-moment comparison, not an analytic moment upper bound.
It instantiates h=hBlock L m, J=blocks samplerA h, c=leafT m h,
s=leafK m h, k=m and n=2J, with I:Instance N m. The supplied selector
equality uses the max cutoff and samplerA>=1 remains explicit. The chosen actual
complement, original tagged C/T and fixed f are preserved.

The selected caller derives c+s=2h and c+m*s+2h<=2J from m+2<=h and
h^2<blocks. With N0=c+m*s, N0<=2^N0 and power monotonicity derive the genuine
rank-loss quotient <=1/2. No selected hsmall or final moment-bound premise is
added. The substantive export casts the actual matching-star Rat mass to Real
and bounds it by twice the SAME coordinate shared-center unconditional append
rank-image moment. The second export preserves the exact Rat center mass beta
under the same selected t/d/m ordered star law.

Frozen Main source SHA256:
`1D84E04486A9045AA6A883D8225B28C253558AD5CC0C47B3289FD817540B0D0B`.
Checks source:
`7BF348B0A60F143241F59F7E335F017F15D178784614EB06E122F62F30641B07`.
Normal objects are Main
`A4F3AD4606ED701ADC6318B95D6AB1767FB6EDC29CB0B7255CC421A8E9EF5A83`
and Checks
`01C103E4A98FF784B023451249C3C407DB4DD3EB32490AB4E08A026058E6AB1E`.

Authenticated Main session80907/PID19104 and Checks session81574/PID9920
both have integer native exit0, success=true, guard_terminated=false,
unchanged source and fresh normal objects. Main output has four unused-name
warnings only; both stderr streams are empty. Focused Checks prints two exact
signatures and both transitive profiles are [propext, Classical.choice,
Quot.sound], with no sorryAx. No optional tests were added.

Seven automatic JSON/stdout/stderr triplets are preserved byte-for-byte under
`docs/native-receipts/ActualSelectedComplementAppendMoment/`. The first five
are native1 diagnostic history, not green. The last two are final Main and
Checks. Final raw JSON hashes are Main
`4D97B20D9B4BE6203B1ED25707A9524AD8B192D43B2A7939D41C008C168A1390`
and Checks
`A6EFE0CCE6A1C0ACCD4B618221C24F7C2CEFC244B648684BD9C18D6075619EDD`.
Their Git-normalized LF hashes are respectively
`96B097A1888EF8DCE4D7DAF517B5F9D593A6A75666B6A13E706215F8E766B9D1`
and `DA22C03B620BEFEE952C4C00D0F74CBCB80E615EE6265EF21DD3E06B5486A151`.
Raw stdout hashes are Main
`4A31C0460EDE57C277229599B541C8B20E8722F9F74347B15638578A1E7F3825`
and Checks
`25795B83942ECB0081E98BDDF5FED24CE71B62A06254A929BC5A92CEB5076386`.
The inspected Python helper1548 and serial native resource guard were used;
the launch reserve and continuous stop are agent operating policy, not a user
mathematical premise. The source-read gate ensured the final calc reused hdim
and actualCoordinateDimensionBound instead of repeating failing arithmetic.

| Top-level lens | Verdict | Bounded scope |
| --- | --- | --- |
| Proof-adversarial (independent reviewer) | GO-WITH-NOTES | Final frozen source and authenticated source/object/receipt/output pins independently verified; exact selected caller and derived rank-loss guards. |
| Complexity-theory (Sol orchestrator) | GO-WITH-NOTES | Genuine selected rank-loss derivation, same C/T/f and joint law; substantial orchestration/arithmetic/name/dimension/calc proof-hint overlap disclosed, no direct proof-source edit or compiler by Sol. |
| Non-claims boundary (independent reviewer) | GO-WITH-NOTES | Independently authenticated all pins and full proof; exact mass-to-moment comparison and Rat beta, supplied selector/sampler/U/A premises, no analytic moment upper-bound or core claim. |

The supplied sourceHMin, U, chosen complement, selector equality and samplerA>=1 are not
existence conclusions. Matching positivity, actual failed-zoom witness,
classical HC/spectral quantitative moment estimate, inverse, robust8S,
numerical NO, runtime, conditional/full core and final consolidation remain
OPEN. Noncomputable coordinate transport is not an efficient strategy claim.
Classical source-contract inhabitants remain outward obligations after core
closure; S3126 and Task/OpenCode fallback review governance debt persists.
The temporary reviewer thread-limit rejection was resolved by sequential
independent reviews, not by substituting an author for the missing lens.
Next analytic work must combine exact source-checked HC/spectral component
fields with a genuine same-leaf level/moment consumer; no existing active Lean
HC/spectral contract was found, and typing a field alone is not force progress.


## UNVERIFIED analytic WIP data checkpoint — 2026-09-30

This checkpoint preserves three owned proof attempts and their raw diagnostic histories; it is not material analytic acceptance or core certification. Main source E84C5224C32E32C0D648827372CBBF4C2DF7E9097EFA4CEE53B11624236334F6 repairs the three remaining native 061304 sites and is not yet checked. Norm helper BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B built as a Linux dependency; full export axiom profiles and three-lens acceptance remain pending. Parameter source 78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582 repairs the sole 060030 width error and is not yet checked.

Latest main run 66503 / 061304 used ED9EDCC9AA65B0506F4F5ECB0A39C65F9F4668855C75A84F6BE4C36602DE7F62 plus BF9C. Native integer exit 1, archive SHA 610E2B83C34BE05CC685E81A89D58BEAF1C269A8C4A4A140E1AC8AB984926945; wrapper confirmed VM TERMINATED. Evidence preserves exact raw output, executed runner and inputs. This is a genuine failed proof diagnostic, not authentication failure.

The exact normalized HC aggregate and conditional HC/spectral moment composition are proof attempts. Actual selected caller, source floor/rho applicability verification, inverse, robust 8S, numeric NO and full core remain open. No final moment assumption is accepted. Original thirteen drafts remain excluded. Sol orchestration and read-only proof hints overlap is disclosed; no final independent reviews are claimed for this WIP checkpoint.


### UNVERIFIED diagnostic checkpoint: durable 064137

Owned run56317 ended with VM TERMINATED. Archive081DE7C41E40C8A75ED5EBC964E8050196B0739B80ACB1737B7E84557B067E69 authenticates parameter prebuild integer0 and main integer1. Frozen source pins51E37/BF9C/78FB are in source-before.sha256. Main has exactly one remaining reported error: Fin.sum_univ_eq_sum_range needs its explicit dimension after the function argument. Actual finite HC/spectral composition otherwise produced no reported errors, but the module is not green. This checkpoint is NOT analytic/core acceptance; no profiles or final lenses are claimed. All stable prepared inputs, actual raw outputs and automatic structured terminal result are durable and byte-backed up. The actual selected caller and inverse/core remain open.


### Build-green intermediate checkpoint: 064926 (not route-final acceptance)

Authenticated run57888 / archive694D8526E6F6B6FE17F1F4B1DA1F75877D7F76B3B253CA490118119A77451482 reports parameter prebuild integer0 and main integer0, no error headers, and authoritative wrapper0/VM TERMINATED. Frozen sources AA22D91A1E6563900B93B826BBAA70638D0D08C9A0A0D5C8B477B51AABCAC09E, BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B, and78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582 have matching before/after hashes. Linux normal objects6AF69AA1E85DC8B9091D0118661B899C10DEA411B3795D74067ECF3E1A456AB4,6C72341582DB34C60E3C0D0F6600EB048A3B1C1996163B4A0D98059005FDAEF5,3AAFAF101F646EAA61891A08670C98D2653142B4D290CF33CF85D03025E35AF1 are pinned. Exact raw evidence and byte backup remain durable.

This builds the conditional finite HC/spectral composition with the exact normalized low-level sum, shared center, Boolean deficient-zero lift, beta domination, and internally proved dyadic window. It does NOT accept source-contract inhabitants, actual selected caller, inverse, decoder, runtime or full core. Material selected caller and focused export axiom profiles plus three independent final lenses remain pending; author/orchestrator hint overlap is retained.


### UNVERIFIED material caller source checkpoint

Draft source0E10B9829D02879DE98351331010A634DD6C8A10083CE64B841CCDDD7D34177C is preserved for data continuity, not acceptance. It adds a genuine center-marginal proof attempt: auxiliary T0(W)=f restricted toW makes all leaves match, then the accepted exact Grassmann law identity and nonempty extension normalization yield the direct center ratio. T0 is solely a proof device for the center marginal; actual T remains the analytic leaf. This addition has not been natively checked.

The material caller attempt now states the full coordinate failed-zoom family and explicit r<leafT+leafK guard, but its current output still incorrectly conjoins theorem proof terms, references a proof-local dimension fact in the declaration, and does not yet consume the accepted actual star comparison into the analytic RHS. These are explicit source defects to repair before another native run, not additional assumptions or accepted claims. Main owner holds this exact draft only for preservation and resumes immediately after commit. Original failure-family coordinate transfer is a distinct active internal proof task. All selected/inverse/core/profile/three-lens debts remain open.
