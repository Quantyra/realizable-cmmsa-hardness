# Actual complement-to-coordinate law bridge

S3126/S3132 next-core dependency audit, 2026-09-29. This is implementation routing evidence, not an inhabited theorem or a classical analytic contract. The current POST-append orthogonality proof remains the first active proof task.

## Existing exact APIs

- `ActualTaggedComplementIncidence.sideComplement_finrank:517`: for the actual `A : SideComplement I copies U`, `Module.finrank (ZMod 2) A.1 = 2 * J`.
- Mathlib `LinearAlgebra/Dimension/Free.lean:340`: `Module.finBasisOfFinrankEq` takes an equality `finrank R M = n` and supplies a basis indexed by `Fin n`. Its `equivFun` supplies the coordinate linear equivalence.
- Mathlib `LinearAlgebra/Dimension/Finrank.lean:121`: `LinearEquiv.finrank_map_eq` preserves the dimension of a mapped submodule.
- `ActualSourceStarLaw.starLaw:88`: the ordered shared-center star law is definitionally `uniformLaw` on `StarTuple`, with nonempty instances derived from `t <= d <= finrank V`.
- `ActualFiniteLaw.pushforward_uniformLaw_equiv:318`: for a finite nonempty equivalence `e : Omega equiv Gamma`, `pushforward e (uniformLaw Omega) = uniformLaw Gamma`.
- `ActualFiniteLaw.eventMass_pushforward:186`: the mass of an event under pushforward equals the mass of its preimage event.
- `ActualOrdinaryStarWeightedSelection.matchingStarMass:49` takes `htd : t <= d`, `hdV : d <= finrank V`, C, T and f and returns Rat. `matchingCenterMass:56` takes the SAME htd/hdV and C/f and returns Rat; BOTH are events under the SAME ordered `starLaw` with t/d/m. The latter carries the same beta used by the analytic consumer.

## Required proof route and concrete targets

For the actual chosen complement A, construct
`E = (Module.finBasisOfFinrankEq (ZMod 2) A.1 (sideComplement_finrank ...)).equivFun`,
with type `A.1` linearly equivalent to `Fin (2*J) -> ZMod 2`.
Map each Grassmann subspace using `Submodule.map E.toLinearMap`; inverse transport uses `E.symm`. Preserve extension containment and prove the sigma-type equivalence of the SAME center with its ordered leaf tuple.

Transport labels by backward composition with the induced restricted subspace equivalences:
`C_E(K_E) = C_A(K).comp(subspaceE.symm)` and similarly for T. Transport the SAME functional by `f_E = f.comp E.symm.toLinearMap`. The input tables must be the already-defined `transportedCenterTable` and `transportedLeafTable` on the actual selected A, not substitute labels with a matching mass premise.

Prove pointwise `MatchesStar` equivalence by `LinearMap.ext` on this exact tuple equivalence. Then consume uniform-law pushforward and event-mass transport to establish BOTH rational targets:

1. `matchingStarMass_A ht hdV C_A T_A f = matchingStarMass_coordinates ht transported_hdV C_E T_E f_E`.
2. `matchingCenterMass_A ht hdV C_A f = matchingCenterMass_coordinates ht transported_hdV C_E f_E`, preserving beta and the same t/d/m joint star law.

Use the actual complement dimensions `n=2J`, `c=t`, `s=2h-t`; selected `t=leafT`, `s=leafK` specialization remains a separate caller obligation. The resulting leaf width is `c+s=2h` under the actual guard. Finrank equality alone does not implement this law/event bridge. Existing internal tagged complement/quotient equivalences do not supply the missing ambient coordinate transport.

After this bridge and the actual operator/energy proofs, apply only source-scoped classical HC/spectral subcontracts with their checked standing assumptions. No field may assume the final actual moment estimate, inverse, robust 8S, numeric NO or conditional core. Classical source-contract inhabitants remain outward obligations after conditional-core closure.
