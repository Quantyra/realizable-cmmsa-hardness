# A7 W6 hybrid-input and normalization bridge

Status: argument-only supplement to `a7-critical-argument-correction.md`, whose mathematical statement corrections remain authoritative. This note addresses the W6 normalization/interface bridge identified in independent review. It separates already available support/coordinate/energy theorems from the remaining typed-to-actual derivative composition. It does not prove that composition or certify A7. No implementation, Lean module, compiler, or Git work was performed.

## Required statement to close the A11-to-Q(f) step

Fix actual finite binary spaces `V,W`, actual subspaces `A <= V`, `B <= W`, an arbitrary outer shift `T : V -> W`, and the complex input `f`. The physical domain of the hybrid derivative is

`P = Hom(V/A, B)`.

Set `g_T : P -> Complex` to the actual function `D_{A,B,T} f`. In current A1 notation this is the complex affine restriction of the ambient hybrid filter:

`g_T(M) = complexAmbientAffineRestrict A B T (complexAmbientHybridFilter A B f) M`.

The A11 application needs the uniform bound, for this fixed outer pair and every outer shift `T`,

`sum over actual frequencies Z : Hom(B,V/A) of rank(Z)<=D, 2^(-6*D*rank Z) * ||D_{Z,0} g_T||_2^4 <= 2 * ||g_T||_2^4`,

with the stronger manuscript constant `67/63` also acceptable. Here the inner derivative `D_{Z,0}` is the W6 rank-additive predecessor filter followed by affine restriction at zero base; it is a function on the physical quotient/kernel carrier `Hom((V/A)/im Z, ker Z)`. The norm is normalized uniform L2 on that actual carrier. Frequencies above `D` contribute zero. This statement must hold with no scalar-F2 hypothesis beyond the actual binary spaces, no extra carrier cardinality factor, and one common outer cutoff `D` for all pairs and shifts.

Then average this pointwise inequality over the actual outer shift `T` and sum over actual outer hybrid pairs `(A,B)`. In the A11 sum the pair/rank-zero term with `|(A,B)|+rank Z=0` is omitted. It may be discarded from the nonnegative W6 left side; the right side is enlarged to the full unweighted `Q(f)`, including `(A,B)=(0,whole)`. No normalization or multiplicity is introduced. The A11 scalar factor `2^(-31*D(k+1))` remains outside this W6 application; W6 supplies the `2^(-6*D*k)` weight and factor at most `2`, giving the manuscript contribution `2^(100*D^2+1-31*D) Q(f)` after the geometric sum.

This required statement is a typed-carrier formulation of manuscript (W6), applied to each actual hybrid derivative input. It is not an assertion that the current code already contains this theorem.

## Physical input versus dual frequency

Keep the two carrier directions distinct:

- physical inputs are `P = Hom(U,B)`, where `U=V/A`;
- Fourier frequencies are the dual `P* = Hom(B,U)`;
- the actual W6 output carrier at frequency `Z` is physically `Hom(U/im Z, ker Z)`.

For bases of `U` and `B`, `carrierMatrixEquiv A B` maps physical `M:P` to its rectangular coordinate matrix. `carrierFrequencyEquiv A B` maps a dual frequency `Z:P*` to a matrix of the same dimensions. Its transpose-aware theorem identifies the transpose linear map of that matrix with the coordinate form of `Z`. Thus its range is exactly the coordinate image of `im Z`, its kernel is the coordinate copy of `ker Z`, and its rank is `finrank(im Z)`. This transpose pairing is essential: using `Z` as a physical carrier element or omitting the transpose would reverse the Hom types. The correction also records Root review clarification 3c08cf/b60fff/f8b652: `g_T` lives on the physical Hom carrier; only its Fourier frequency lives on the dual Hom type.

Let `m=finrank U`, `r=finrank B`, and let `g#(K)=g((carrierMatrixEquiv A B).symm K)` on `BinaryMatrix r m`. The existing accepted coordinate equivalence supplies both directions:

1. Every physical `M:P` maps to `K=carrierMatrixEquiv A B M`; inverse is `K -> (carrierMatrixEquiv A B).symm K`.
2. Every dual `Z:P*` maps to `Y=carrierFrequencyEquiv A B Z`; inverse is `Y -> (carrierFrequencyEquiv A B).symm Y`.
3. `carrierFrequency_tracePair` preserves the actual duality pairing; hence character values and Fourier phases agree under the two maps.
4. `carrierFrequency_rank` identifies `rank(Y)` with `finrank(range Z)`.
5. `carrierFourierCoeff_coordinate` identifies typed and coordinate Fourier coefficients exactly.
6. `carrierMean_coordinate` / `carrierComplexEnergy_coordinate` preserve the normalized physical uniform mean because the maps are equivalences and their finite carrier cardinalities agree. In particular,
   `carrierMean A B (fun M => Complex.normSq (g M)) = uniformMean (fun K => Complex.normSq (g# K))`.
   Squaring both sides is exactly `||g||_2^4 = (uniformMean (fun K => Complex.normSq (g# K)))^2`; there is no dimension or cardinality multiplier.
7. `carrierFourier_support_iff_coordinate` transports degree support in both directions, using the same actual rank.

The physical output for inner frequency `Z` must likewise be identified in both directions with the actual W6 carrier for `Y=carrierFrequencyEquiv A B Z`: the domain quotient `U/im Z` is equivalent to the coordinate quotient by `range(Y^T)`, and `ker Z` is equivalent to `ker(Y^T)`. The resulting equivalence on Hom carriers must intertwine the affine restriction bases, quotient inclusions, and dual trace pairing. This is the output-carrier equality needed to identify the two normalized L2 fourth powers, not only a cardinality argument.

## Comparing selector, derivative, and support

In coordinates, the parent frequency for the W6 theorem is `Y=carrierFrequencyEquiv A B Z`. Its matrix predecessor relation is `w6Precedes Y Y'`, meaning `rank(Y')=rank(Y)+rank(Y'-Y)`. The typed statement must transport this relation exactly to the manuscript relation `Z preceq Z'`. The coordinate map is linear and transpose-aware, so this is expected from rank preservation on both a difference and its summands, but the exact equivalence of selected finite sets must be stated; a rank-only theorem is insufficient for a Fourier sum.

For each selected inner frequency, the character phase at zero base must agree under `carrierFrequencyEquiv` and `carrierMatrixEquiv`. The same selected set, coefficients, and phases then give equality of the typed `D_{Z,0}g` and `actualW6Derivative Y 0 g#` after the output-carrier equivalence. This is the no-extra-factor derivative identity. Merely comparing Parseval sums is insufficient if frequencies collide; the identity must preserve the actual grouped coefficient sums.

The support step is available in the current source. `filteredCarrierFunction` is definitionally the exact physical function `g_T` above. `filteredCarrierFunction_supportedThrough` in `ActualBinaryMatrixHC46A20SquareSupport.lean` proves carrier Fourier support through the original `D` for every actual `(A,B,T)` from only `ComplexFourierSupportedThrough D f`. Its proof uses `filteredCarrierFunction_support_drop` when the fixed rank cost fits under `D`; if the cost exceeds `D`, the filtered carrier function is zero. `carrierFourier_support_iff_coordinate` then transports this result to `g#_T`. Thus this portion adds no premise and no cutoff loss. The support transport is available; it does not by itself identify the W6 derivative output carrier.

## Exact current W6 interfaces and their coverage

Manuscript (W6), for an ambient coordinate function `h` supported through `D`, states

`sum_X 2^(-6*D*rank X) * ||D_X h||_2^4 <= (67/63) * ||h||_2^4 <= 2 * ||h||_2^4`,

where `D_X = D_{X,0}`. Its proof includes the exact `D=0` endpoint, where the weighted sum is `||h||_2^4`.

The current actual-coordinate theorem is `actualW6Derivative_weighted_fourth_moment_le_67_63` (and the weaker `..._le_two`) in `ActualBinaryMatrixHC46A7EnergyConsumer.lean`. It is pointwise in a base `T`, accepts any ambient complex `h` plus `ComplexFourierSupportedThrough D h`, and concludes

`sum_X (carrierMean (range X^T) (ker X^T) (fun M => normSq (actualW6Derivative X T h M)))^2 / 2^(6*D*X.rank) <= (67/63) * (uniformMean (fun M => normSq (h M)))^2`.

The squared carrier mean is precisely the fourth power of normalized L2 of the actual derivative. Choosing the inner W6 base `T=0` gives the manuscript `D_X`; the theorem is stronger in allowing arbitrary bases. `actualW6Derivative_weighted_fourth_moment_degree_zero_eq` gives the exact degree-zero endpoint. Its hypotheses have no extra scalar-field input, conditional rank premise, or frequency-collision exclusion.

Other relevant exact declarations:

- `actualW6Derivative` and `w6PredecessorFilter` in `ActualBinaryMatrixHC46A7WeightedPredecessor.lean`;
- `w6ActualCarrierFrequency` and `w6ActualPredecessorFrequencyFiber`, plus `w6_actual_predecessor_frequency_fiber_card`, in that module;
- `complex_carrier_parseval` and `actualW6Derivative_energy_parseval` in `ActualBinaryMatrixHC46A7CarrierParseval.lean`;
- `actualW6Derivative_carrierCoeff_fiberSum`, the actual fiber Cauchy/energy bounds, and `actualW6Derivative_fourierEnergy_fiber_partition` in `ActualBinaryMatrixHC46A7EnergyConsumer.lean`;
- `carrierMatrixEquiv`, `carrierFrequencyEquiv`, `carrierFrequency_toLin`, `carrierMatrix_toLin`, `carrierFrequency_tracePair`, `carrierFrequency_rank`, `carrierFourierCoeff_coordinate`, `carrierComplexEnergy_coordinate`, and `carrierFourier_support_iff_coordinate` in `ActualBinaryMatrixHC46TypedFourierTransport.lean`;
- `complexAmbientHybridFilter`, `complexAmbientAffineRestrict`, and `manuscript_A1_complex` in `BinaryMatrixA1Complex.lean`;
- `filteredCarrierFunction` in `ActualTypedABCanonicalDCollapse.lean`, definitionally the same `g_T`;
- `filteredCarrierFunction_support_drop` / `actualDerivativeCoordinate_support_drop` in `ActualBinaryMatrixHC46A18DerivativeRankProjection.lean`, and the all-cost `filteredCarrierFunction_supportedThrough` in `ActualBinaryMatrixHC46A20SquareSupport.lean`.

These establish the two coordinate equivalences, normalized input mean, coefficient/character/rank/support transport, support preservation for the exact hybrid derivative input, and a full-scope actual W6 theorem on coordinate matrix spaces. In particular, degree support through the same `D` is already available from `filteredCarrierFunction_supportedThrough`; it is not an unresolved mathematical implication. The audit did not find a single checked theorem composing those facts for `g_T=D_{A,B,T}f`, identifying its coordinate W6 derivative with the manuscript typed inner derivative on `Hom(U/im Z,ker Z)`. Nor did it find the exact theorem averaging that bound over the outer shift and summing all actual hybrid `(A,B)` into the manuscript A11 `Q(f)` with omitted zero-order pair/rank endpoint handled as stated.

## Required exact composition, with no factor loss

The sufficiency bridge must prove these equalities/implications in order:

1. Define `g_T` on the physical carrier `P=Hom(V/A,B)` from the actual complex A1 hybrid filter plus affine restriction.
2. Prove `CarrierComplexFourierSupportedThrough A B D g_T`; transport it to `ComplexFourierSupportedThrough D g#_T` using `carrierFourier_support_iff_coordinate`.
3. Apply `actualW6Derivative_weighted_fourth_moment_le_two` to `g#_T` at inner base zero. Its RHS is exactly `2*||g_T||_2^4` by normalized-mean preservation.
4. For every coordinate parent matrix, identify its typed frequency `Z` and actual output carrier in both directions; prove equality of the actual coordinate derivative and typed `D_{Z,0}g_T`, with equal selected sets, phases, and rank. Use `carrierFourierCoeff_coordinate` and trace-pair preservation, not a proxy carrier or an orthogonality assumption.
5. Convert the actual carrier mean square to `||D_{Z,0}g_T||_2^4` with no factor. Reindex the full finite sum by the frequency equivalence. Average over outer `T`, then sum outer `(A,B)`; use nonnegativity to enlarge the A11-restricted sum to all pairs as appropriate. Retain the explicit zero-order term `||f||_2^4<=Q(f)` and the manuscript `D=0` base endpoint.

## Remaining proof obligations

1. Use `filteredCarrierFunction_supportedThrough` plus `carrierFourier_support_iff_coordinate` to supply the same-`D` support hypothesis; `filteredCarrierFunction` is definitionally `g_T`.
2. Typed-selector/coordinate-predecessor equivalence for every frequency, both directions, including rank of differences and equality of selected finite sets.
3. Nested output carrier equivalence `Hom((V/A)/im Z,ker Z) ~= Hom(V_m/range(Y^T),ker(Y^T))` with actual evaluation/affine base and both inverse laws.
4. Equality of inner typed derivative and `actualW6Derivative Y 0 g#_T`, including phases and grouped coefficient sums under collisions.
5. No-factor proof for the L2 normalization on the nested carrier and conversion to the exact fourth-power term in A11.
6. Pointwise-in-outer-shift averaging and outer-pair summation, matching the unweighted all-hybrid `Q(f)` including zero; handle the A11 omitted zero pair/rank-zero term by nonnegativity and retain the separate zero-order control.

The accepted W6 theorem and current support theorem make the numerical weighted estimate available once the exact selector, nested output-carrier, derivative, normalization, and outer-sum transports are proved. W6 does not by itself prove those transports. A7 implementation remains premature until independent review accepts this bridge argument and the unresolved implications are addressed.