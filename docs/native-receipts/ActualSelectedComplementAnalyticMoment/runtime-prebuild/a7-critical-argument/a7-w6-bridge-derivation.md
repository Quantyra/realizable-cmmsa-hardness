# A7 W6 bridge: explicit carrier derivation

Status: detailed mathematical derivation supplement to `a7-critical-argument-correction.md` and `a7-w6-hybrid-input-normalization-bridge.md`. This discharges the coordinate/carrier/selector/derivative/normalization bridge on paper, subject to the exact Lean composition listed at the end. It is not a kernel proof or an A7 certification. The earlier bridge's support claim is conditional on the pinned source object/evidence for the cited support theorem; this note does not freshly certify that object. No implementation, module edit, compiler, or Git work was performed.

The scope is the manuscript A7 setting: arbitrary finite binary spaces, complex `f`, Fourier degree at most `D`, and the unweighted sum `Q(f)` over all actual hybrid pairs including `(0,whole)`. The parameter `D` is degree, not an ambient dimension. Root's correction `3c08cf/b60fff/f8b652` is followed: physical input and dual frequency Hom spaces have opposite directions.

## 1. Input carrier, coordinates, and inverses

Fix actual `A<=V`, `B<=W`; put `U=V/A`. Let

`P = Hom_F(U,B)` (physical inputs), and `P* = Hom_F(B,U)` (Fourier frequencies).

Choose any linear equivalences `u : U ~= F^m` and `b : B ~= F^r`, where `m=dim U`, `r=dim B`. Define the physical matrix-coordinate equivalence

`e_M(M) = b o M o u^{-1} : Hom_F(F^m,F^r)`.

Its inverse is explicit:

`e_M^{-1}(K) = b^{-1} o K o u`.

Both inverse laws follow by composition cancellation:

`e_M^{-1}(e_M(M)) = b^{-1} (b M u^{-1}) u = M`,

`e_M(e_M^{-1}(K)) = b (b^{-1} K u) u^{-1} = K`.

After the standard function-space/matrix equivalence, these are the concrete maps underlying `carrierMatrixEquiv` and its `symm`. This is a bijection of the entire physical finite carrier, not a map into a larger ambient space with multiplicity.

For a dual frequency `Z:B->U`, define

`Z# = u o Z o b^{-1} : F^r -> F^m`.

The inverse is `Z = u^{-1} o Z# o b`. Again both laws are direct cancellation. Under the matrix conventions, `Z#` is `carrierFrequencyEquiv A B Z`: its transpose-linear-map interpretation is the coordinate representation of `Z`, as stated by `carrierFrequency_toLin`. In particular,

`rank(Z#) = dim(range Z)`, `ker(Z#)=b(ker Z)`, and `range(Z#)=u(range Z)`.

The direction matters: `K=e_M(M)` maps the physical `U->B` input to an `r by m` matrix, whereas `Z#` maps the dual `B->U` frequency to an `r by m` matrix in the pairing convention. The transpose-aware representation identifies its transpose map with `Z`; no physical input is reinterpreted as a frequency.

## 2. Pairing, Fourier coefficients, support, and normalized input energy

The actual carrier pairing is `tracePair Z M = trace(Z o M)` (equivalently the cyclic trace on `B`). With `K=e_M(M)` and `Z#` as above,

`Z# o K = u o (Z o M) o u^{-1}`.

Trace is invariant under this conjugation, so `tracePair Z M = matrixPairing Z# K`; therefore the character values are equal pointwise. This is precisely the content of `carrierFrequency_tracePair` / `carrierFrequency_character`, not an orthogonality argument.

Define `g#(K)=g(e_M^{-1}(K))`. The finite Fourier coefficient on `P` is the normalized sum

`hat_g(Z) = (1/|P|) sum_{M in P} g(M) chi_Z(M)`.

Use the bijection `e_M` in this sum and the character equality just proved. Since `|P|=|Hom(F^m,F^r)|`,

`hat_g(Z) = hat_{g#}(Z#)`.

This is the exact equation `carrierFourierCoeff_coordinate`. The maps on frequencies are bijective with inverse `Z# -> u^{-1} Z# b`; consequently the entire Fourier expansion transports in both directions and preserves any collisions among induced output frequencies by keeping every summand.

Normalized mean is equally exact. The bijection `e_M` gives

`(1/|P|) sum_M normSq(g(M)) = (1/|Hom(F^m,F^r)|) sum_K normSq(g#(K))`.

This is `carrierComplexEnergy_coordinate` (or `carrierMean_coordinate`). Thus normalized `||g||_2^4`, which means the square of the normalized mean of `normSq(g)`, is exactly the corresponding coordinate quantity. There is no factor of `|P|`, `2^(mr)`, or a quotient cardinality. `carrierFrequency_rank` and `carrierFourier_support_iff_coordinate` show that support through the same `D` is preserved in both directions.

For the required input use

`g_T(M) = complexAmbientAffineRestrict A B T (complexAmbientHybridFilter A B f) M`.

This is definitionally `filteredCarrierFunction A B T f` in the current source. The current declaration `filteredCarrierFunction_supportedThrough` proves carrier support through the same `D` for every actual pair and outer shift, from support of `f` through `D`; it uses the exact rank-cost drop when the cost is at most `D`, and proves the carrier function zero when the cost exceeds `D`. `carrierFourier_support_iff_coordinate` then proves support of `g#_T`. This use of the source theorem is conditional on the cited declaration belonging to the accepted/pinned source object; no fresh build/certificate is asserted here.

## 3. Output carrier: quotient and kernel maps with inverse laws

Fix a typed frequency `Z:B->U`. Let `I=range Z` and `K0=ker Z`. The typed physical output carrier is

`P_Z = Hom_F(U/I,K0)`.

For `Z#`, let `I#=range Z#` and `K#=ker Z#`. Since `I#=u(I)` and `K#=b(K0)`, `u` induces a quotient equivalence

`ubar : U/I ~= F^m/I#`, `ubar(x+I)=u(x)+I#`,

with inverse `ubar^{-1}(x#+I#)=u^{-1}(x#)+I`. Well-definedness in each direction follows from `u(I)=I#`; both inverse laws are the quotient-map inverse laws induced by `u^{-1}u=id` and `uu^{-1}=id`.

Restrict `b` to kernels:

`bker : K0 ~= K#`, `bker(x)=b(x)`,

whose inverse is the restriction of `b^{-1}`. Kernel membership is preserved in both directions since `Z#(b(x))=u(Z(x))` and `u` is injective.

For `N:P_Z`, define its physical output coordinate map

`N# = bker o N o ubar^{-1} : F^m/I# -> K#`.

The inverse is

`N = bker^{-1} o N# o ubar : U/I -> K0`.

Composition cancellation gives both inverse laws, pointwise. Hence this is a bijection between *all* typed output points and *all* actual W6 carrier points; no fiber cardinality or assumed multiplicity enters.

At matrix parent `Y=Z#`, the actual W6 carrier is

`P_Y# = Hom_F(F^m/range(Y^T), ker(Y^T))`.

The transpose-aware frequency theorem identifies `range(Y^T)=I#` and `ker(Y^T)=K#`, so `ubar` and `bker` above are exactly the required quotient/kernel identifications. The coordinate matrix of the embedded physical input corresponding to `N` is

`K_N = inclusion(K# -> F^r) o N# o quotient(F^m -> F^m/I#)`.

This equals `e_M(inclusion(K0 -> B) o N o quotient(U -> U/I))` by substituting `N#=bker N ubar^{-1}` and cancelling `u,b`. Thus evaluation of the carrier function at the affine restriction point agrees in both models. This proves the required output-point correspondence in both directions, rather than only an equality of cardinalities.

The output carriers have equal finite cardinalities by this equivalence. Applying the same normalized-mean argument as for the input gives exact equality of normalized L2 energy of corresponding output functions, and therefore of their fourth powers. Again there is no dimension or carrier-size factor.

## 4. Selected-set equivalence and the grouped derivative identity

For typed frequencies `Z,Z' : B->U`, define `Z preceq Z'` by

`rank(Z') = rank(Z) + rank(Z'-Z)`.

The coordinate map is linear: `(Z'-Z)#=Z'#-Z#`. It preserves ranks of `Z`, `Z'`, and their difference. Therefore

`Z preceq Z' <-> w6Precedes(Z#,Z#')`.

This is both directions and identifies the selected finite sets bijectively. The existing actual theorem `w6Precedes` uses exactly the matrix rank-additivity equation; the remaining formal application is to instantiate rank preservation for the difference as well as the two terms.

Use the Fourier expansion definition of the typed W6 operator at zero base:

`D_{Z,0}g(N) = sum_{Z' : Z preceq Z'} hat_g(Z') * chi_{Z'}(embed_Z(N))`,

where `embed_Z(N)` is the quotient/subtype inclusion point in `P`. The actual matrix W6 definition is

`actualW6Derivative Y 0 g#(N#) = sum_{Y' : w6Precedes(Y,Y')} hat_{g#}(Y') * character(Y', matrixPoint(N#))`.

Reindex the latter finite sum by the frequency equivalence `Z' <-> Y'=Z'#`. The selected predicates agree by the preceding rank-additivity equivalence. Fourier coefficients agree by Section 2. Character values agree because

`(Z'#) o K_N = u o (Z' o embed_Z(N)) o u^{-1}`,

so the trace is unchanged by conjugation. The affine base is zero on both sides; if retaining a displayed base parameter in the actual API, instantiate it with the zero linear map. Thus each corresponding summand is equal, including its coefficient and phase, and `Fintype.sum_equiv` gives

`D_{Z,0}g(N) = actualW6Derivative Z# 0 g#(N#)`.

This is an equality of grouped finite sums. If distinct `Z'` induce the same output frequency or character, both corresponding terms remain in the sums with their multiplicity; no orthogonality, distinct-frequency, or collision-fiber cardinality hypothesis is used.

The same derivation at an arbitrary actual inner base `S` gives the phase `chi_{Z'}(S+embed_Z(N))` on the typed side and the equal coordinate character on the actual side. The manuscript W6 uses base zero, so zero suffices for A11.

## 5. Exact no-factor W6 application and outer summation

For each fixed actual outer `(A,B,T)`, let `g_T` and `g#_T` be as above. Conditional on the existing support theorem's pinned object, `g#_T` is supported through the same degree `D`. Apply the current pointwise theorem `actualW6Derivative_weighted_fourth_moment_le_two` with input `g#_T` and inner base `0`:

`sum_Y (carrierMean_{P_Y#}(normSq(actualW6Derivative Y 0 g#_T)))^2 / 2^(6*D*rank Y) <= 2 * (uniformMean(normSq(g#_T)))^2`.

By the output equivalence and derivative identity, every squared carrier mean on the left is exactly `||D_{Z,0}g_T||_2^4`. By the input equivalence, the RHS is exactly `2*||g_T||_2^4`. Reindex `Y <-> Z` using `carrierFrequencyEquiv`; ranks match. This proves the required typed W6 inequality with no factor. The stronger `67/63` theorem is not needed. The current theorem is pointwise in its inner base `S`, so the choice `S=0` requires no new estimate. For `D=0`, `actualW6Derivative_weighted_fourth_moment_degree_zero_eq` supplies the exact equality endpoint; for positive `D`, frequencies above `D` vanish by support/degree lowering.

Now fix outer `(A,B)`, average this bound over the original uniform `T`, and sum over all outer pairs. Finite sums commute with this average. The right side becomes exactly `2 Q(f)` because `g_T=D_{A,B,T}f` and `Q(f)` is the unweighted sum over every actual pair, including `(0,whole)`. In A11 the pair/rank-zero term with `|(A,B)|+rank Z=0` is omitted, and the rank sum is presented only through `D`; enlarging to the full W6 sum is valid by nonnegativity, with rank `>D` terms zero. The full outer right side still uses every pair in `Q(f)`. The zero-order term gives `||f||_2^4<=Q(f)` exactly as in the corrected A7 argument.

Finally, the A11 coefficient is

`2^(-31*D*(k+1))*2^(-4*D*k) = 2^(-31*D-29*D*k)*2^(-6*D*k)`.

For fixed outer pair and shift, the factor `2^(-29*D*k)<=1` can be discarded after the actual W6 estimate. The W6 factor `2` and the geometric sum over initial dimensions give `2^(100*D^2+1-31*D)Q(f)`, exactly the manuscript endpoint. No second average, `Fintype.card` ratio, or carrier-size factor is introduced. The degree-zero *induction* case remains separate and has equality from the zero-order hybrid derivative; the zero-degree W6 formula is consistent with it.

## 6. T1 `X` versus `R`: pullback required for rank order

There is a related typing precision at T1. The descended isomorphism is

`Xbar : H/B ~= A/C`.

The restriction map is a different map

`R = q_C o Y|H : H -> V/C`.

The rank-poset relation cannot compare `Xbar` directly to `R`, since their domains and codomains differ. Pull `Xbar` back to `H` and include its target:

`Xtilde = inclusion(A/C -> V/C) o Xbar o quotient(H -> H/B) : H -> V/C`.

Then `Xtilde(b+z)=Yz+C`, its kernel is `B`, and its image is the embedded `A/C`. Also

`(R-Xtilde)(b+z)=Yb+C`,

whose image is `Y(B)/C`. These images are disjoint because `C=Y(B) intersect A`; their sum is the image of `R`. Hence `rank R = rank Xtilde + rank(R-Xtilde)` and `Xtilde preceq R`. The quotient-level isomorphism remains the triple parameter; its pullback is the actual same-typed map needed in the rank order. This distinction is required in any formal T1 transport.

## 7. Exact current declarations versus certification boundary

Current source declarations supporting the argument include:

- `filteredCarrierFunction` (`ActualTypedABCanonicalDCollapse.lean`), definitionally the complex A1 hybrid filter followed by affine restriction;
- `filteredCarrierFunction_supportedThrough` (`ActualBinaryMatrixHC46A20SquareSupport.lean`), same-D support for every actual outer pair/shift, with the cost-too-large zero case;
- `carrierMatrixEquiv`, `carrierFrequencyEquiv`, `carrierFrequency_toLin`, `carrierMatrix_toLin`, `carrierFrequency_tracePair`, `carrierFrequency_rank`, `carrierFourierCoeff_coordinate`, `carrierComplexEnergy_coordinate`, `carrierFourier_support_iff_coordinate` (`ActualBinaryMatrixHC46TypedFourierTransport.lean`);
- `w6Precedes`, `w6PredecessorFilter`, `actualW6Derivative`, and its Fourier expansion/coefficient formulas (`ActualBinaryMatrixHC46A7WeightedPredecessor.lean`);
- `complex_carrier_parseval`, `actualW6Derivative_energy_parseval` (`ActualBinaryMatrixHC46A7CarrierParseval.lean`);
- `actualW6Derivative_weighted_fourth_moment_le_67_63`, `..._le_two`, and `..._degree_zero_eq` (`ActualBinaryMatrixHC46A7EnergyConsumer.lean`).

On paper the explicit equivalences above compose these interfaces into the desired W6-to-A11 statement. The remaining formal work is to instantiate and compose them with exact types, especially the nested quotient/kernel output map and equality of selected finite-sum operators. Existing coordinate/support declarations are evidence for their individual steps, not a fresh certification of their pinned build object. This derivation does not assert an accepted compiler result, a new source theorem, or full A7 sufficiency; Root must assess it separately before implementation.