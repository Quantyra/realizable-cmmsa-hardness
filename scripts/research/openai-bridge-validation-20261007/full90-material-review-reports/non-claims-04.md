# Non-claims review: material-consumer packet 4/5

## Verdict for this packet only: GO-WITH-NOTES

- **Coverage.** I read the full body of all 36 supplied files and skipped none.
- **No blocking findings.** I found no vacuous main statement, no hidden extra premise, no inequality pointing the wrong way, and no overclaim that the code contradicts.
- **What the notes concern.** The notes are about scope and attribution: what this packet's files must not be credited with, what the evidence covers, stale provenance text, one parameter-fidelity question, and the Complexitylib boundary.
- **How I reviewed.** No tools, no Lean, no hashing. Compilation, the source pins and the fresh-173 axiom profile come from the receipts you supplied. I cite findings by declaration name, not line number.
- **What this verdict does not cover:**
  - It is not a verdict on the material moment, and material readiness stays INCOMPLETE.
  - It does not review any of the 23 Complexitylib bodies. None of them is in this packet.
  - It does not credit any root.

## File coverage (36 inspected, 0 skipped)

"Consumed" is the pinned `transitively_consumed` flag.

| File | Consumed | Disposition |
|---|---|---|
| ActualTaggedConcreteStarLaw | **true** | Inspected. Law construction only; selection depends on `hcenter`/`hleaf`. |
| ActualTaggedFixedCenterGeometry | **true** | Inspected. Its header correctly describes it as an exploratory spike that defines no test. |
| ActualTaggedFixedTableAcceptance | **true** | Inspected. Event interface plus completeness for an honest global assignment. |
| ActualTaggedOrderedSampleNonempty | **true** | Inspected. Explicitly makes no claim about NO-side soundness. |
| CoveringSpan | **true** | Inspected. Carries a stale UNCOMPILED banner (N1). |
| CoveringTV | **true** | Inspected. Carries a stale banner; its "bridge OPEN" note is true only of this file (N1, N5). |
| EqualityGadget | **true** | Inspected. Constant gadget proved with `decide`; header accurate. |
| FixedPortCycleFamily | **true** | Inspected. Stale "not compiled" banner; Complexitylib consumer (N1, N3). |
| ActualTaggedComposedPhysicalSampler | false | Inspected (N4, N5). |
| ActualTaggedConditionalDomainCollision | false | Inspected. Header overstates its content (N5). |
| ActualTaggedConditionalDomainDraw | false | Inspected. |
| ActualTaggedFixedUDensityForce | false | Inspected. One stale docstring (N4, N5). |
| ActualTaggedMZSideDraw | false | Inspected (N4, N10). |
| ActualTaggedOrderedClassCollisionBound | false | Inspected. |
| ActualTaggedOrderedFullLawForce | false | Inspected. Depends on an external comparison lemma. |
| ActualTaggedOrderedQuestionSourceBridge | false | Inspected (N6). |
| ActualTaggedPresentationFiberAudit | false | Inspected. |
| ActualTaggedPresentedSelection | false | Inspected. |
| ActualTaggedQuestionMass | false | Inspected (N10). |
| ActualTaggedQuestionRetainedMass | false | Inspected (N6, N10). |
| ActualTaggedSelectedDecoderBridge | false | Inspected. |
| ActualTaggedTargetPresentationInvariant | false | Inspected. |
| ActualTaggedVertexPhysicalAcceptance | false | Inspected. |
| ActualTaggedVertexPhysicalLaw | false | Inspected. |
| ActualTaggedVertexPresentationFiber | false | Inspected. |
| ActualTypedMixedTower | false | Inspected. Record type only; proves no A15 bound (N12). |
| AdviceExceptions | false | Inspected (N1, N5, N8). |
| BernoulliMGF | false | Inspected. |
| ConditionedCovering | false | Inspected (N1, N8). |
| DropCountTail | false | Inspected (N1). |
| DropTailParameters | false | Inspected (N1, N8). |
| ExceptionRepair | false | Inspected (N9, N10). |
| ExpanderCutInstantiation | false | Inspected (N1, N3). |
| FiniteConcentration | false | Inspected. |
| FiniteSampling | false | Inspected. |
| Formula | false | Inspected (N9). |

## Mathematical checks (all hold as written)

**Counts and conditional laws**
- The conditional presentation fibre has `2^(J(2h−t))` elements.
- The full-domain draw is `Gaussian(2J−t, 2h−t)`. That follows from coordinate dimension 3J, centre span `t+J`, and a quotient of dimension `2J−t`.
- Each vertex has `2^(J·2h)` presentations. Each ordered-good fibre has `J!` elements.
- All uniform pushforward identities are exact pointwise atom equalities.

**Class collision**
- For two leaves with the same `U`, being in the same class is equivalent to having equal domains (imported lemma). So each index pair collides with probability exactly `1/Gaussian`.
- A union bound over pairs gives `C(k,2)/Gaussian`, which is at most `2^-J` under `hexp` (Gaussian ≥ 2^(2J)) and `k² ≤ 2^J`.

**Selection and threshold forcing**
- Representative selection: physical acceptance ≤ the average of selected acceptance + collision ≤ selected(s*) + collision. The inequality points the right way.
- Forcing from the threshold:
  - The averaging lemma takes "mean ≥ β with values in [0,1]" to "mass ≥ β/2 above β/2".
  - With q+6 ≤ p ≤ J: `(1/2)^J + 16·(1/2)^p ≤ (17/64)(1/2)^q ≤ (1/2)^(q+1)`.

**Question mass**
- Bad mass ≤ `157·J(J−1)/(K·rows)`. Padding gives ≤ 1/T, which is ≤ 1/4. Good mass ≥ 3/4, and the conditioning factor is ≤ 4/3.

**Covering**
- Cube chi-square = `β²((N²+2N)/3 − 1) ≤ β²N²`. Hellinger tensorises under products, and TV² ≤ Hellinger².
- The span-kernel failure correction `βJ(2^a−1)/2^J` is absorbed into `β√J·2^a`, giving the `2^(a+4)` constant.
- KMS conditioning: averaged conditional TV ≤ 2·TV. Markov then gives bad-zoom mass ≤ `√β·J^(1/4)`.

**Tails and repair**
- Chernoff `(eμ/T)^T`: the zero-mean case and `0^0` are handled explicitly.
- `Ready ⇒ base ≤ 1/2`, and `h⁴ ≥ 100h²`.
- `exception_soundness` arithmetic: `3σs/8` bound, `avg e ≤ 3γ/8`, final value `< 2γ`.

**Equality gadget**
- Summing the rows forces x = y. The extension a=c=e=0, b=x, d=y attains exactly `mismatch` violations.

## Findings

| ID | Severity | Declarations | Finding and disposition |
|---|---|---|---|
| N1 | Medium (provenance) | Banners in AdviceExceptions, ConditionedCovering, CoveringSpan, CoveringTV, DropCountTail, DropTailParameters ("UNCOMPILED"), and ExpanderCutInstantiation, FixedPortCycleFamily ("not compiled") | These contradict the receipt showing all 319 files compiled. Three of the eight are consumed. The banners carry no weight either way; compile status rests only on the receipts. Remove them before render. |
| N2 | Medium (scope) | All files with `transitively_consumed: false` (28 of 36) | These have compile evidence only and no fresh axiom profile. That covers the tagged sampler laws, presented selection, collision bound, ordered and full-law force, MZ side draw, composed sampler, KMS covering, exceptional advice, Chernoff, concentration and repair. None may be credited to the material root, and source/star/robust8S stays **OPEN**. The pins also point to how much reaches the trace (this is an inference that per-constant trace membership needs to confirm): `TaggedLeafOver`/`sampledStar` would pull in PresentedSelection (false), so only the question/centre carrier of ConcreteStarLaw is reached. `actual_adviceTV_le_manuscript` would pull in AdviceExceptions (false), so the KMS bound is not reached. |
| N3 | Medium (Complexitylib boundary) | FixedPortCycleFamily `degree`, `base`, `graph`, `table`; ExpanderCutInstantiation `boundary_expansion`, `port_cut_of_spectral`, `fixedCoefficient` | The consumed family is defined from `Complexity.algFamily` plus `relabel`/`ofRot`, which matches the four directly reached boundary modules (FamilyFin, RegularGraph, Expander, ExpanderPad). The expansion results (`kappa`, `cut_expansion`) go through ExpanderCutInstantiation (not consumed) and Cheeger, which is not a direct boundary module. So the material trace appears to reach the family's definitional data, not its expansion theorem. The source itself disclaims FP/runtime ("not itself an FP claim", "not an encoded bitstring-machine theorem"). Nothing here establishes `SpectralBound` semantics, coverage of every n (padding), uniformity of λ<1, or computability. Those stay open as a Complexitylib review obligation and are not proved by citation. |
| N4 | Medium (fidelity) | `ordered_manuscript_half_value_forces_MZ_threshold_U`, `composedScore_gt_forces_MZ_threshold_U`, `composedLegalValue_gt_forces_MZ_threshold_U`, `composedLegalValue_gt_forces_side_threshold_U` | With `autoImplicit false`, the `m` in `hp`/`hq`/`hlarge` is the section variable from `Instance N m`. The proofs use only `q+6 ≤ p`. "Manuscript parameter" readings need the manuscript's m to be confirmed as the same as the instance's m. If they differ, cite only the `hgap` form. |
| N5 | Low (stale or overstated text) | FixedUDensityForce docstring ("composed→physical … unproved"); AdviceExceptions ("TV proximity … undisclosed"); CoveringTV ("bridge OPEN"); ConcreteStarLaw header; ConditionalDomainCollision header ("ordered class-collision mass") | The first is superseded by `composedTaggedScore_eq_orderedPhysicalMass`, an equality between two Lean definitions. Whether `composedDomainScore`/`composedLegalValue` faithfully model the manuscript's composed verifier has not been reviewed. The second and third are superseded within CoveringSpan. The ConditionalDomainCollision header overstates: the file contains only the fibre count. |
| N6 | Medium (sampler conditioning) | `orderedGoodLaw`, `orderedStarLaw`, `actual_tagged_conditioning_factor_*` | The ordered law is uniform on *good* tuples, i.e. already conditioned. A loss factor (≤4/3) is proved, but no theorem in this packet charges it inside the force chain. Integration has to decide which law the manuscript's verifier actually draws from. |
| N7 | Low (conditional) | All `*_forces_*` theorems | Each concludes only that a predraw canonical `T'` has an eligible-U mass at or above a density threshold. Docstrings explicitly deny any MZ decoder conclusion, NO-side soundness or numeric NO. Do not cite them for robust8S or numeric NO. |
| N8 | Low (not assembled) | AdviceExceptions, DropTailParameters, ConditionedCovering | Exceptional advice + TV + Chernoff + ζ are never combined into a single theorem; DropTailParameters explicitly disclaims doing so. `actual_conditioned_covering` assumes `a<d`, but its proof uses only `a≤d`. |
| N9 | Info | `#print axioms` in ExceptionRepair and Formula | These emit info messages whose output was not supplied. They are not evidence, and those declarations carry no fresh profile. |
| N10 | Info (hygiene) | ActualTaggedQuestionMass/RetainedMass; ExceptionRepair; MZSideDraw; ActualTypedMixedTower | The QuestionMass/RetainedMass files place declarations in the `ActualQuestionMassBridge` namespace instead of a namespace matching the module. ExceptionRepair defines generic `average`/`weight` in a shared namespace. MZSideDraw shadows the section variables `J`/`U`. In ActualTypedMixedTower the type name repeats the namespace. Also: `maxHeartbeats 2000000` and fragile `convert!`/`try simp` steps. |
| N11 | Info | EqualityGadget `decide` lemmas | Consumed and checked by the kernel. Correctness of this constant gadget does not imply source hardness, as the header says. |
| N12 | Info | `ActualTypedMixedTower` | Records the typed tower data and proves only the termination measure `length_le_total_finrank`. `hL`/`hv`/`hv0` are stored but constrain no bound. It is not consumed. |

## Cross-packet questions retained for integration

1. **Per-constant trace membership** for the eight consumed modules. This would confirm or refute the inferences in N2 and N3.
2. **Complexitylib (23 bodies, other packets).** Needed: the definition of `algFamily` (choice or random-permutation existence versus explicit construction), `SpectralBound` and its normalisation, `spectral_graph`, `lam_lt_one`/`lam_nonneg`, `degree_pos`, `spectralBound_relabel`, `ofRot`/`deg_ofRot`, `sum_darts_boundary`, `card_dartsBetween_compl_ge`, padding/merge reindexing, and any claimed computational bound.
3. **External lemmas** used by this packet:
   - `tagged_physical_le_canonical_plus_collision` and `tagged_class_eq_iff_domain_eq_sameU`;
   - `choose_mul_twoNegTwoJ_le_twoNegJ`, `gaussian_small_over_large_le` and `card_conditional_complements`;
   - `conflict_degree_le`/`tagged_bad_ordered_question_count_*` (the 157), `rowId_incidence_card_le_four`, and the `equationSpan_*` lemmas;
   - `GoodQuestion`, `cut_expansion` (PortCycleReplacement), and the TripleRestriction*/GrassmannFlagPosterior/PosteriorDensity APIs.
4. **Manuscript fidelity:** the m identity (N4), the composed and side-conditioned MZ tests, the conditioned ordered law (N6), the strict `a<d` in KMS 4.7, and the `2^(-k h²)` reading.

## Safe conditional claim for this packet

Under the qualified native receipts and pinned library trust, these 36 files compile and contain sound, non-vacuous finite-law, counting, covering, tail and repair lemmas. Every NO-side force statement among them stays conditional and stops short of a decoder or soundness conclusion.

They contribute to the material root only through carrier and type-level data, which is a bounded inference from the pins. That data includes `Complexity.algFamily` through FixedPortCycleFamily.

Nothing here supplies or supports:
- Spectral47, numeric NO, or source/star/robust8S closure;
- expander or runtime guarantees, or Complexitylib acceptance;
- manuscript fidelity;
- any whole-manuscript verdict.
