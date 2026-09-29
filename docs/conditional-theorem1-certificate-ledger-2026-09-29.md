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
| Outer hardness and smooth repeated game | MZ Theorem 3.1, Section 3.2, Claim 3.2; fixed absolute 3-Lin NO gap, arbitrarily small fixed positive YES error, bounded occurrence, and game value `≤2^{-Ω(η² 2^{-r} βJ)}`. Manuscript Section 3, `paper/body.tex:55`. | **External**. No encoded SAT-to-outer `SeededMap` with all quantifiers and the game bound is proved here. |
| Star construction and label transport | MZ Section 3.3, Lemmas 3.3–3.4; legitimate `U`, transverse `K,L_i`, side-condition-preserving unique transport, weighted `(m+1)`-star, finite enumeration. Manuscript `paper/body.tex:57`. | **External** for construction/transport. Tagged physical-law and representative-selection Lean modules prove selected new comparisons, but do not construct the full encoded reduction. |
| Scoped local decoder | MZ Theorem 4.2; fixed `U`, density at least `S=2^{-2(1-1000ρ)hm}`, `a+c≤10m/ρ`, lucky `Q` mass at least `2^{-6h²}`, and agreement `C=2^{-2(1-1000ρ²)h}/5`. Manuscript `paper/body.tex:59`. | **External at source scope only**. The changed-ambient robust `8S` application is a manuscript-new obligation, not an imported all-`J` decoder theorem. Existing `ActualTaggedFixedUDensityForce` reaches the `8S` input but does not yield the decoder conclusion. |
| Maximal-pair counting | MZ Definition 5.4 and MZ24 revision 1 Theorem 5.26, with `δ=ρ/m`, fixed subsidiary constants, `dim V≥2^h`, dimensions/codimensions `≤10m/ρ`, threshold `B≥2^{-2(1-(ρ/m)^3)h}`, and count `≤B^{-2}2^{O_{m,ρ}(h)}`. Manuscript `paper/body.tex:61`. | **External**. The descending threshold ladder and use in changed ambient are manuscript-new. |
| Covering | KMS Definition 4.5, Lemmas 4.6–4.7, Section 8; independent triple-deletion sampler and its joint-law conditioned advice bound, including exceptional `Q` mass. Manuscript `paper/body.tex:63`. | **External**. The posterior, vector-law and zoom-out comparisons for this parameter order remain manuscript-new. |
| Weighted star compilation | HN Definition 4.4 and Lemma 4.6; one global center/leaf partition, `m≥1`, deletion of zero-occurrence vertices, normalized occurrence weights, repeated leaf-variable consistency, leaf bound `(m+1)R`, budget `1/Λ`, exact-weight YES, monotonicity, and real-threshold base NO satisfaction at most `3/4`. Manuscript `paper/body.tex:65` and Section 8. | **Typed external finite-semantic contract** in `ActualCoreSourceContractScopes.ExternalHNWeightedStarCompiler`, uniformly over valid finite stars; no inhabitant is proved. Its `HNSourceStar` preconditions enforce the source applicability scope, and `HNCompilationConclusion` uses the actual finite `compile`/weight semantics. The polynomial-time encoded formula-distribution constructor is absent. This contract does not supply AND sampling, finite-list repair, rounding, or an encoded source-to-CMMSA map. Strict `<γ_L` is obtained only downstream. |

These entries describe mathematical source contracts, not Lean axioms.
The MZ24 count and finite-semantic HN compiler have explicit external Lean
interfaces; faithful typing of the remaining source contracts and encoded
interfaces remains work. A broad `hSrcCmmsa` parameter would absorb
manuscript-new work.

## Lean facts already available for the manuscript-new comparison

- `ActualTaggedCanonicalNoComparison.tagged_physical_le_canonical_plus_collision`
  selects one predraw representative table for an arbitrary fixed legal table
  with explicit class-collision loss. The conditioned original-score bridge
  and `ActualTaggedFixedUDensityForce.ordered_manuscript_half_value_forces_MZ_threshold_U`
  feed the fixed-`U` robust input. They do not prove a decoder conclusion.
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
  chain and asymptotic family for its current selector. Its placeholder
  `manuscriptSourceFloor n = n+2` must be reconciled with the actual cutoff.
- `ActualTheorem1.theorem1_realizable_cmmsa` composes assumed SAT-to-source
  and source-to-CMMSA `Preserves (1/6)` maps with Cook–Levin. It is a
  conditional assembly theorem; its broad source-to-CMMSA premise is **not**
  one of the cited contracts and does not certify the core result.

## Remaining manuscript-new obligations before core closeout

1. Prove the changed-ambient robust `8S` local decoder application from the
   scoped MZ fixed-`U` contract, including all matrix-lift, inverse-explicit,
   positive-rank, posterior, and zoom comparisons needed for its exact query
   law and quantified `a,c,Q,W,g` conclusion. The current `8S` mass bound is
   only its input. Preserve arbitrary fixed legal tables and the explicit
   representative-class collision charge.
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
5. Replace `n+2` in the parameter selector by the actual fixed-parameter
   cutoff and re-establish eventual admissibility/asymptotics for the selected
   `m(L)`. Then connect the concrete SAT-to-outer and outer-to-CMMSA
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
