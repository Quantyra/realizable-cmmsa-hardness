# Actual original-law amplification through the H-side witness

Status: uncompiled source offer. This file records the mathematical composition and exact API boundary of the current Lean source. It makes no compilation, acceptance, global decoder, or unconditioned-zoom claim.

## Fixed data and source-level API bindings

Fix the actual instance `I`, copies, good question `U`, and selected numeric data `(L,m,samplerA,base,cutoff)` with the original selector equality. Put

- `h = hBlock L m`, `J = blocks samplerA h`, `t = leafT m h, d = leafT m h + leafK m h = 2h, k = m`, `r = numericRankThreshold m`, `e = refreshThreshold m h`, and `S = successMargin (badExponent m h)`;
- `U : TaggedGoodU I copies J`;
- `C : TaggedCenterTable I copies` and the same globally fixed `T : TaggedLeafTable I copies` used in the actual side-density premise.

The center and leaf tables are predrawn once. For each actual side complement `A : SideComplement I copies U`, use the existing fixed-frame constructors

`C_A := selectedCoordinateCenterTable I copies U A C`

and

`T_A := selectedCoordinateLeafTable I copies U A T`.

Both live in the *same* `CoordAmbient J`, where its finrank is `2J`. They are induced from the actual complement restrictions `transportedCenterTable A C` and `transportedLeafTable A T`, followed by `coordinateCenterTable` and `coordinateLeafTable` for the same `actualCoordinateEquiv A`. The fixed-frame lemma `starDensity_coordinate_eq` identifies the complement's ordinary `StarDensity` for those actual restrictions with the coordinate `StarDensity` of `(C_A,T_A)`. The complement-mass offer's `transportedStarDensity` is the exact star-density quantity passed to the local selected-refresh argument; its existing bridge is `complementFullAcceptMass_le_transportedStarDensity` and the globally averaged result `sideDensity_le_original_complement_mean`.

The assembly carries the explicit ambient identity `J = blocks samplerA h`; it does not infer this relation from the side sampler type. In every star density the repetition arity is `k=m`; `samplerA` determines only the ambient dimension `J`.

Required original premise: `8*S <= sideConditionalDensity I copies U (leafT m h) h m C T` (with the concrete leaf-dimension indices normalized using `d=2h`). Also retain `0<=S`. No law is conditioned on a good or successful complement.

## Positive mass of actual complements

Instantiate `ActualComplementDensityMass.original_good_complement_mass_lower` with the same globally predrawn `(C,T)` and the original `sideConditionalDensity` premise. Its set is

`G := { A | 4*S <= transportedStarDensity A C T }`

and its measure is `originalComplementLaw`, exactly uniform on all actual side complements with atom `1 / #SideComplement`. The result is

`4*S <= eventMass (originalComplementLaw I copies U) G`.

This is the original unconditioned complement mass. The proof uses `transportedStarDensity_nonneg_le_one` to bound the mean by `4*S + mass(G)` and never changes the denominator.

From the selected numeric height bounds, derive `h<=J`, `d=2h`, `t<=2h`, and `d<=2J`; `gaussian_pos` and `extension_nonempty` then provide the nonempty center and leaf carriers required by v2, uniformly in the complement because the coordinate ambient is fixed. For every `A in G`, the captured v2 theorem `ActualSelectedRefreshCoverAverageV2.selected_coordinate_refresh_cover_margin_four` applies to the concrete coordinate tables `(C_A,T_A)` in `CoordAmbient J`, after identifying `J=blocks samplerA h` and `d=2h`. Its premises are the unchanged selected instance, `A>=1`, the actual center support and leaf nonemptiness in that coordinate carrier, and `2*S <= StarDensity(C_A,T_A)`. The latter follows from `4*S <= transportedStarDensity A` and the exact fixed-frame density identity (or the already pinned transported-density equality). It proves the strict local bound

`S / (2*m*2^(4*h^2)) < sum_{a : Fin (r+1)} goodAdviceFraction (T_A) e a`.

Thus, with `D := S / (2*m*2^(4*h^2))`, each complement in `G` satisfies the weak premise `D <= sum_a fraction(A,a)` required by `ActualDistinctAdviceAverage.original_law_summed_fraction_lower`.

## Average under the original complement law and choose one dimension

Apply `ActualDistinctAdviceAverage.exists_dimension_original_law_fraction_lower` to

- `Omega := SideComplement I copies U`;
- `mu := originalComplementLaw I copies U`;
- `T(A) := T_A` (all refresh tables have the same `CoordAmbient J` and leaf dimension `d`);
- the actual unconditioned good set `G` and `D` above.

It gives one `a : Fin (r+1)` for which

`eventMass mu G * D / (r+1) <= originalLawAdviceFraction mu (fun A => T_A) e a`.

Since `mass(G)>=4*S` and `D=S/(2*m*2^(4*h^2))`, nonnegativity of `S` gives

`2*S^2 / (m*2^(4*h^2)*(r+1)) <= originalLawAdviceFraction mu (fun A => T_A) e a`.

No good-complement normalization is used. This is an expectation over the full original mu, and the dimension is selected only after averaging.

## Actual successful `(A,Q)` event and mass comparison

For this chosen `a`, define `success(A,Q_A)` on the actual source sampler by the actual decoded-pair/H-side witness. Here `Q_A : Grass A.1 a.val`, `qcoord := grassCoordinateEquiv I copies U A Q_A`, and `T_A` is the fixed-frame transport of the same globally predrawn T. Require an actual pulled-back pair `P_A := pullbackDecodedPair A qcoord Pcoord` with `a.val + codim P_A.W = r`, strict ordinary agreement `e/2 < (agreement (transportedLeafTable A T) Q_A P_A : Real)`, and the H-window extension built from `W' := P_A.W`, `g := P_A.g`, and

`F := sideExtensionMap A W' (sideCanonicalRhs I copies U) g`.

The witness uses the actual H-window extension `F` on `sideWindow A W' = H + W'.map A.subtype`. In the current source, `actualComplementSuccess` requires an exact-budget decoded pair and strict ordinary agreement against `transportedLeafTable A T`; `actualComplementSuccess_has_H_extension` then constructs the canonical H-side extension and proves its two restriction identities. The public amplification endpoint carries this actual witness through the favorable event. It does not yet include an agreement-ratio premise on the full conditioned `SideFullDomain` law.

The implication from coordinate `goodAdvice` to actual complement success is derived, not assumed. A local coordinate pair contains `qcoord <= Pcoord.W`; the inverse Grassmann equivalence and `pullbackDecodedPair` give `Q_A <= W'`. The fixed-frame APIs `pullbackDecodedPair_codim` and `pullbackAgreement_eq` preserve codimension and the exact ordinary agreement ratio against `transportedLeafTable A T`. The H-side extension APIs prove the H and W restriction identities. The separate H11 APIs `actual_transverse_agreement_iff` and `actualOriginalTable_transverseAgreement_ratio` concern a raw-vertex table and representative choice; binding those APIs to this source's `TaggedLeafTable` success event and full conditioned-domain ratio remains a separate step. The actual budget is preserved: `sideWindow_finrank_budget` gives `finrank(sideWindow A W') + codim_A(W') = 3J`, while `pullbackDecodedPair_codim` preserves `a.val + codim_A(W') = r`.

A finite-set injection by `grassCoordinateEquiv A` and the pullback witness proves, for each fixed A and a, that the coordinate `goodAdvice` fraction is at most the actual-complement success fraction. This is the implemented `coordinate_fraction_le_actual_success_fraction`; it needs only the forward witness transport, not a converse decoder construction. The uniform denominator is preserved by `Fintype.card_congr`. Separately, finite-sum regrouping proves that the literal joint A-first success sum

`sum A, sum Q_A, (1/#SideComplement) * (1/#Grass(A,a)) * 1_success(A,Q_A)`

is exactly the expectation under `originalComplementLaw` of `actualComplementSuccessFraction A`. Combining the pointwise fraction inequality with the captured original-law averaging theorem yields the same numeric lower bound for the actual A-first success event. Every complement remains in the original law with its original weight.
For the favorable full-space predicate define `P(Q_E)` to mean that there exist an actual complement A, `Q_A : Grass A.1 a`, and the actual W'/g/H-window witness above, with `Q_E = Q_A.map A.1.subtype`. This predicate is existential over A; it does not select, condition on, or renormalize a favorable complement. `centerInComplementEquiv A a Q_A` identifies the embedded actual advice subspace with its transverse `SideCenter` carrier. The pointwise implication `success(A,Q_A) -> P((centerInComplementEquiv A a Q_A).1.1.val)` is witnessed by that same A and the constructed H extension.
The public source endpoints are `actualComplementSuccess`, `actualComplementSuccess_has_H_extension`, `coordinate_fraction_le_actual_success_fraction`, `actualAfirstEventMass_eq_originalComplementExpectation`, `exists_dimension_actual_original_law_success_lower`, and `actualHWindow_success_mass_le_transverse`. The last endpoint is the exact H9 incidence-law step; it subtracts no nontransverse mass by itself.

## Exact incidence law and full-space advice correction

Apply H9's `actual_original_Afirst_complementAdvice_event_le_transverse_event` to the arbitrary complement-dependent `success(A,Q_A)` just defined and the just-proved pointwise implication. This theorem reindexes the literal A-first weights above through `actualComplementAdviceIncidenceEquiv` and the exact `actualAdvice_complement_fiber_mass`; it gives a lower bound of the same size on

`eventMass (uniformLaw (SideCenter I copies U a)) {K | P(K.1.val)}`.

Use `uniform_sideCenter_pushforward_transverseAdvice` and the explicit `sideCenterEquiv_allTransverseAdvice` to rewrite this as the conditional ratio of P among *all and only* advice subspaces transverse to H. Then invoke `actualAllAdvice_transverseEvent_mass_lower`. It subtracts the explicit all-Q nontransverse mass

`1 / 2^(2*J-a-1)`

from the transverse event fraction, under the actual guards `a<=3J` and `J+a+1<=3J`. The resulting bound is on the original uniform all-Q law in `Grass(E,a)` for `Q transverse to H and P(Q)`, with the same H-side witness. This correction is a separate additive term; it does not identify unconditioned full zoom agreement with conditioned transverse agreement.

## Precise dependency/API checklist

- Captured `numeric-complement-mass-capture-v1`: `originalComplementLaw`, `originalComplementLaw_mass`, `sideDensity_le_original_complement_mean`, `goodComplementSet`, `original_good_complement_mass_lower`.
- Captured `numeric-advice-average-capture-v1`: `originalLawAdviceFraction`, `original_law_summed_fraction_lower`, `exists_dimension_original_law_fraction_lower`, `good_advice_fixed_codimension`.
- Captured `numeric-fixed-frame-transport-capture-v3` / offered v3: `selectedCoordinateCenterTable`, `selectedCoordinateLeafTable`, `starDensity_coordinate_eq`, `pullbackDecodedPair`, `pullbackDecodedPair_codim`, `pullbackAgreement_eq`.
- Captured selected refresh v2: `ActualSelectedRefreshCoverAverageV2.selected_coordinate_refresh_cover_margin_four` (local density-to-distinct-Q bound; its source closure pins the fixed selected inverse, actual refresh preservation, good cover, Gaussian counting, and selected height/spectral APIs).
- H11 captured v11 (module `ActualNumericSideExtension`): `sideCanonicalRhs`, `sideWindow`, `sideWindow_finrank_budget`, `sideExtensionMap`, `sideExtensionOnWindow`, `sideFullDomainExtension_restrict_ordinaryLeaf`, `transportedLeafTable_eq_actualFullDomain`, `actual_transverse_agreement_iff`, `actualOriginalTable_transverseAgreement_ratio`, `actual_original_Afirst_complementAdvice_event_le_transverse_event`, `actualComplementAdvice_event_mass_reindex`, `uniform_sideCenter_pushforward_transverseAdvice`, `sideCenterEquiv_allTransverseAdvice`, and `actualAllAdvice_transverseEvent_mass_lower`. The v11 statement-time `Nonempty` repair is needed for the public law-valued endpoint.

## True remaining proof obligation / boundary

The source offer now includes the concrete numeric theorem that applies the captured v2 margin-four bound to each actual complement in G, instantiates `original_good_complement_mass_lower`, averages with the full `originalComplementLaw`, and selects one advice dimension. This endpoint is `actual_original_law_amplification`; its output is an actual A-first success mass with the original complement and advice atom weights. The proof still requires native elaboration and review; no compile or acceptance is claimed.

The output currently retains the actual H-window extension and ordinary complement-table agreement, but does not yet assert the full conditioned-domain agreement ratio. Root is handling the separate binding and dyadic-loss route; do not claim an all-leaf or unconditioned full-zoom identity. Decoder uniformity across all advice, robustness amplification, source NO, random-history, runtime, and certification remain outside this offer.

Remaining to-do list: obtain independent capture and native elaboration/axiom review. Do not claim an unconditioned full-zoom identity.

## V3 inclusion API repair

The pinned Mathlib API declares both submodule endpoints of `Submodule.inclusion` implicitly. V3 changes the single H-window restriction occurrence to `Submodule.inclusion (show H I copies U ≤ sideWindow I copies U A W' from le_sup_left)` and binds the disjoint H12 source offer. The theorem statement and mathematical argument are unchanged; V2 and H11 remain preserved captured inputs. This remains source-only and uncompiled.
