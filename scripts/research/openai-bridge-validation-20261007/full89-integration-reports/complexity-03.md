# Full89 independent complexity review: integration window 3/3 (carrier counting and transport)

## Verdict

**This window: GO-WITH-NOTES.** It covers only the 12 supplied bodies and the cross-partition counting and transport contracts they carry.

**Overall Full89 integration: INCOMPLETE.** The HIGH questions about the HC46 contract and the material consumer depend on bodies that are not in this window (OriginalExactInhabitant, ActualSelectedComplementAnalyticMoment, BinaryMatrixFourier, A11, A22, RealQ*, the matrix-lift files). I retain them below. This verdict does not accept any milestone and is not a full-manuscript verdict.

## How I reviewed

- I used no tools, made no writes and ran no Lean, Lake or subagents. Nothing was written to `…\qualification\review-sources`.
- I cite declarations by name. I did not count line numbers.
- I checked the stdout independently: there are exactly **172** `depends on axioms` entries (A8 26, A11 23, A12 18, A16 1, A20 4, A18 3, A21 9, A17 1, RealQNorm 14, RealQTransport 32, A22OperatorLq 10, A22ParentFactorization 13, A22OriginalInduction 10, HC46 6, selected 2). Every profile is a subset of {propext, Classical.choice, Quot.sound}. `a21_exponent_le` is {propext}, and `a21_density_recurrence` is {propext, Quot.sound}.
- `#print axioms` reports transitive closure. So standard profiles on the four consumers cover every constant they reach in this window. Declarations they do not reach carry no axiom evidence and get no credit.
- I took the following from the qualified receipts and did not re-derive them: compile status, the 319 source pins, the 566 warm objects, and the toolchain identities.
- Zero *owned* warnings and zero inherited regressions are not the same as zero *total* warnings. Inherited baseline warning debt stays open.
- Init, Mathlib and Batteries are trusted at their pinned versions. I did not newly review them.

## Bodies inspected: 12 supplied, 12 inspected, 0 skipped

| # | File (SHA256 prefix) | Status |
|---|---|---|
| 1 | A7T1Transfer (300CD79D) | inspected |
| 2 | A7WeightedPredecessor (775FFB87) | inspected |
| 3 | A8AmbientAssembly (BE845673) | inspected |
| 4 | A8AveragedAssembly (0C5D9127) | inspected |
| 5 | A8AveragedTransport (83191C84) | inspected |
| 6 | A8Endpoint (61387FFD) | inspected |
| 7 | A9AmbientFiber (024850F6) | inspected |
| 8 | A9AmbientReindex (5B4958CE) | inspected |
| 9 | CommonA16 (5B200903) | inspected |
| 10 | FourierA16 (21E062E1) | inspected |
| 11 | ActualTypedABFullA16Assembly (BECC6381) | inspected |
| 12 | ActualTypedABFullA16Final (A592FF69) | inspected |

I reused the prior reports only for these unchanged hashes.

## Window findings and dispositions

### Resolved from this window's source

**R1. A16 has no cost premise; constant 2^(11D²).** Resolves packet2 proof F2, complexity Q2 and non-claims A20 cost.
- `filteredCarrierFunction_energy_le_A16` quantifies over every A, B, T and f. Its only premises are `hsupport` and `hglobal`, and `0 ≤ eps` is derived from them.
- The zero-carrier branch (A=⊥, B=⊤) uses the order-0 restriction directly.
- Levels below dim A + codim B are annihilated by `selected_frequency_rank_lower_bound`.
- Each retained level costs at most 2^(10D²)·eps. Residual ranks are orthogonal through `retained_rank_representation` and `typedComplexRankProjection_cross_orthogonal`. The final step is (D+1) ≤ 2^(D²).
- This explains why A20 can ignore `_hcost`.

**R2. `typedW6Precedes` is definitionally `t1RankPrecedes`, with the same orientation.** Resolves packet3 complexity N1 and non-claims F6.
- In `t1PointwiseFull_fourierIdentity`, `hactive_iff` closes by `rfl`.
- In `a8_actual_energy_zero_outside_supported_window`, `change` unfolds `typedW6Precedes A B Y Z` to rank Z = rank Y + rank(Z−Y).
- The orientation is: predecessor X is the pullback, and Z is the original restriction.

**R3. The actual A9 fibre is non-degenerate.** Resolves packet5 F4/N8 within this window.
- `A9AmbientA0` requires A0 ≤ A with dim i. `A9AmbientB0` requires **B ≤ B0** with codim j, which is the manuscript's direction.
- `A9AmbientInitialDatum` carries the `induces` field.
- `a9Ambient_A8_sideConditions_iff_rank_preservation` is proved in both directions.
- `a9AmbientA8PartitionEquiv` is an exact bijection: both inverse laws hold, by `rfl` and by `subst`.
- `a9_ambient_fiber_card` = G(a,i)·G(b,j)·2^(k(a−i))·2^(k(b−j)). I re-derived each factor: the section kernel has dim a−i, B0/B has dim b−j, and the B0 count is G(b,b−j) = G(b,j) by annihilator counting only.
- The legacy `A9InitialGraph` is not used by these bodies. The claim that it is absent from the trace remains bounded to Root's exact172/focused-four scope.

**R4. The A8 endpoint and A9 contracts match.**
- The endpoint's indicator `A'⊓(range X).comap C.mkQ = C ∧ B'⊔(ker X).map H.subtype = H` is literally `a9AmbientA8SideConditions`, with A0 = C and B0 = H.
- The index dimensions are fixed by `rfl` (i = dim C, j = codim H).
- The energy expression is identical to `a9AmbientA8Energy`.
- The endpoint's k is the initial rank of X. A9 uses the final rank of Y. These are equal because of rank preservation.
- The 2^(6Dk) factor is identical on both sides.

**R5. A8 averaging and cubic cost.** I re-derived this.
- The complement count is cubed exactly once, at each fixed (T, S0).
- The square stays inside both averages. There is no Jensen step that merges them.
- The S0 average is removed only by `Equiv.addRight` translation in T, and card ΩS cancels exactly.
- In `a8_supported_graph_charge`:
  - If cost ≤ D, then u+v ≤ cost ≤ D, so 3k(u+v) ≤ 3Dk ≤ 6Dk.
  - If cost > D, the energy is 0.
  - The stated 6Dk therefore has a factor-2 slack in the exponent. It is valid and conservative.

**R6. DR6 filter bridge (packet6 non-claims Q2).**
- `t1OrdinaryProjection_affineExpansion` rewrites the selector of `DR6ComplexOrdinaryFilter` to `DR6OrdinarySelected` using `dr6_complexSelector_iff_actualOrdinary`.
- `t1SelectedTheta` forces the shape of `DR6OrdinarySelected` to be A ≤ range Yᵀ ∧ ker Yᵀ ≤ B.
- Whether that matches the manuscript is still retained.

**R7. A7 predecessor fibre.** `w6_actual_predecessor_frequency_fiber_card` is universal and exact at 2^(2·rank X·l). Rank additivity is re-derived in the backward map, not assumed.

### Partially resolved

**P1. Support-window case split for the A9 coarse charge.**
- `a9Ambient_fixed_fiber_coarse_charge` needs a+b+k ≤ D.
- Its complement case, D < dim A + codim B + rank Y, has zero energy by `a8_actual_energy_zero_outside_supported_window`.
- Both halves exist. Whether A11 actually performs the split is retained.

**P2. Offset-0 specialization (packet3 N3).** The local derivative is `actualW6Derivative Xmat 0 (actualDerivativeCoordinate C H T f)`, so T enters through the coordinate. The identification with `a7OutputBinary` relies on `a8_output_coordinate_eq`, whose body is not in this window.

**P3. Upper bound on Q (packet4 non-claims note 5).** This window supplies the T-averaged *output* Q bound against the actual final predecessor energies. Linking it to the original Q is A11's job and is retained.

### New in this window

**N1 (Medium, retained). Some imported modules are outside the 170 selected files.**
- These bodies import modules that are not in the 170 selected set: `A9ActualFiber` (imported by A9AmbientFiber), `MixedPeeling`, `CommonDerivative` and `FinitePeeling` (imported by CommonA16, FourierA16 and A16Final).
- The constants visibly on the route do not come from them:
  - A16 uses only `complexEnergy_finite_sum_of_orthogonal` and `rankProjection_inner_eq_zero`.
  - A9 uses W6Grass and w6Gaussian from A7PredecessorCount.
- Still needed: per-constant module membership from the trace, showing that no constant reached by the four consumers is defined in these modules. Without that, they would be required bodies that were never reviewed.

**N2 (Low).** `a8_output_q_le_actual_predecessor_sum`:
- `_horder` is unused, so the caller must still discharge it.
- Its docstring says "no support-window premise", but it requires `hsupport`.

**N3 (Low).** The A8AveragedAssembly and A8AveragedTransport headers claim acceptance at frozen runs 46/56. These are comments and carry no weight.

**N4 (Info).** Private definitions (`a9AmbientA8Energy` and the duplicated `complexRealDot` copies) appear in public statements and are bridged by unfolding. A7WeightedPredecessor closes its section early. A8AveragedTransport contains dead private lemmas. None of this affects soundness.

## HIGH and Medium questions retained across windows

**H1. hHC in the same material-moment consumer.**
- Suppose `original_HC46_exact` has exactly the universal type `HC46ExactContract`. Root and the packet1 reports say it does, but the body is not in this window. Then `selected_actual_material_moment_bound (hHC := original_HC46_exact)` is logically available on the same T and f.
- None of the 172 roots is a dedicated hHC-free material export.
- `hSpectral` (Spectral47) and `hfail` remain premises, and the numerical bound has not been shown to be useful.
- Missing evidence: the exact statements of `HC46ExactContract`, `original_HC46_exact` and `selected_actual_material_moment_bound`, plus a compiled instantiation term.

**H2. Is the contract inconsistent or vacuous?** (packet7 proof F2)
- If the type ascription above holds, a kernel-checked standard-axiom inhabitant rules out refutability. The stdout shows a standard profile.
- The proposed counterexample (eta=0, b≡true) fails only if the padded exact-r whole fibre (`exactWholeRestriction`) exists for every r.
- The negative-eta case, zero density, `boolean_mean_le_of_exact`, and the definition of `PseudorandomExact` are not in this window.
- This stays HIGH until it is confirmed against BinaryMatrixFourier and ActualBinaryMatrixHC46.

**Retained, bodies absent from this window:**
- **A11's discharge of hS from the strict lower-degree hypothesis.** The A8/A9 contracts it consumes are confirmed non-degenerate (R3, R4).
- **Packet3 F2.** Accounting for the T1 triple count across t.
- **Budget mechanics.** Nominal padding, actual exact-budget flag averaging, the strict r<d and c<k guards, the same predrawn T and f, and the factor 2.
- **`PseudorandomExact` is one-sided.** It is a density upper bound only, as packet9 says.
- **A22 scope.** Natural dyadic p with q = `pConjugate p`, plus the A18/A21/A22 constants and their dependency direction.
- **Influence definition.** Whether it includes order 0 (manuscript fidelity).
- **The rest.** DR6 signed normalization, Spectral47, useful numeric bounds, the source/star/robust8S/numericNO, encoded-reduction, runtime and learning lanes, upstream bridges, fresh checkout, the final provider, and manuscript/render/novelty.

## What can safely be claimed

The 12 bodies in this window establish the following, assuming the qualified native receipts and the pinned library trust:
- Exact T1, A7, A9 and A8 carrier counting and transport.
- An arbitrary-complex A8 output-Q bound with the 2^(6Dk) budget, derived from support.
- The cost-unconditional 2^(11D²) A16 bound.
- Contract-level agreement between the A8 endpoint and the actual A9 fibre and partition.

Nothing more follows from this window. In particular it does not establish the hHC-free material moment, the reduction, runtime or learning results, or any acceptance of the manuscript.
