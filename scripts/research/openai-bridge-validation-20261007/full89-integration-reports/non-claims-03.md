# Full89 integration, window 3/3 (carrier counting and transport): independent non-claims review

**Verdict for this window: GO-WITH-NOTES.** I found no defect in the 12 supplied bodies. Their contracts with the neighbouring files are consistent with every adjacent statement visible in this window and in the prior reports.

**The integration as a whole stays INCOMPLETE.** Several required items can't be settled from this window's source:
- the A11 hS assembly;
- the A18, A21 and A22 bodies;
- the OriginalExactInhabitant and OriginalApplication bodies;
- one Medium coverage gap (finding W3-M1 below).

No full-manuscript verdict is given or implied.

**Method.** I used no tools, wrote nothing, ran no code, Lean or Lake, and used no subagents. Compilation, axiom profiles, source pins and object identity all come from the supplied native receipts; I did not reproduce them. I can't count lines without tools, so citations are by declaration name.

## 1. Coverage: 12 of 12 supplied complete bodies inspected, none skipped

Each SHA label below matches its entry in the all170 pin list. I compared labels only and did not recompute any hash.

| File | SHA (label) | Status |
|---|---|---|
| ActualBinaryMatrixHC46A7T1Transfer | 300CD79D… | inspected in full |
| ActualBinaryMatrixHC46A7WeightedPredecessor | 775FFB87… | inspected in full |
| ActualBinaryMatrixHC46A8AmbientAssembly | BE845673… | inspected in full |
| ActualBinaryMatrixHC46A8AveragedAssembly | 0C5D9127… | inspected in full |
| ActualBinaryMatrixHC46A8AveragedTransport | 83191C84… | inspected in full |
| ActualBinaryMatrixHC46A8Endpoint | 61387FFD… | inspected in full |
| ActualBinaryMatrixHC46A9AmbientFiber | 024850F6… | inspected in full |
| ActualBinaryMatrixHC46A9AmbientReindex | 5B4958CE… | inspected in full |
| ActualBinaryMatrixHC46CommonA16 | 5B200903… | inspected in full |
| ActualBinaryMatrixHC46FourierA16 | 21E062E1… | inspected in full |
| ActualTypedABFullA16Assembly | BECC6381… | inspected in full |
| ActualTypedABFullA16Final | A592FF69… | inspected in full |

The other 158 bodies are not in this window. For them I rely only on the 27 prior reports and their pinned identities.

## 2. Cross-partition contracts checked in this window

**C1. A8 endpoint matches the A9 source exactly.**
- `a8_output_q_le_actual_predecessor_sum` sums over pairs `(A' ⊇ C, B' ⊆ H)`.
  - Guard: `A' ⊓ (range X).comap C.mkQ = C ∧ B' ⊔ (ker X).map H.subtype = H`.
  - Final map: `a9AmbientFinalMap` with `A0 := ⟨C,…,rfl⟩` and `B0 := ⟨H,…,rfl⟩`.
- That guard is literally the predicate in `A9AmbientA8Source` and `a9AmbientA8SideConditions`, with `A0=C`, `B0=H`, `A=A'`, `B=B'`.
- The summand `finalEnergy` (private, in A8Endpoint) has the same body as `a9AmbientA8Energy` (private, in A9AmbientReindex): the T-mean of the squared `typedW6OutputEnergy` of `filteredCarrierFunction A B T f`. The source is the original `f`, the average is over the original ambient `T`, and the square stays inside the average.
- Both use `k = finrank range X`; `carrierFrequency_rank` converts it to `Xmat.rank`.
- So the endpoint fixes `(C,H,X)` and sums over finals, while A9 fixes `(A,B)` and sums over `(A0,B0,X)`. **Swapping the summation order (Fubini) is the A11 consumer's job and is not in this window.**

**C2. Supported-window case split.**
- `a9Ambient_fixed_fiber_coarse_charge` requires `hfin : a+b+k ≤ D`, with `a = dim A`, `b = codim B` and `k = rank Y`.
- The complementary case is covered exactly by `a8_actual_energy_zero_outside_supported_window`: if `D < dim A + codim B + rank Y`, the energy is 0. I checked both of its branches:
  - when `c ≤ D`, `filteredCarrierFunction_support_drop` applies, because the predecessor's rank is at least `rank Y`;
  - when `c > D`, every rank projection at index `i ≤ D < c` vanishes.
- So the split is available at the contract level. Whether A11 actually performs it is question X2 below.

**C3. Exponent budgets (recomputed).**
- **A8 graph charge** (`a8_supported_graph_charge`): the complement count is ≤ `2^{k(u+v)}`. Cubing once gives `2^{3k(u+v)}`, and `u+v ≤` cost `≤ D` gives `≤ 2^{3Dk}`. The stated `2^{6Dk}` is valid with a factor-2 slack in the exponent.
  - The cost identity is `a8_nested_ambient_cost`: cost = dim C + codim H + dim p.1.1 + codim p.1.2.
  - The case cost > D goes to the zero-energy lemma.
- **Cubic Cauchy step** (`a8_complex_normalized_mean_cube`): E ≤ mΣe, then E² ≤ m²(Σe)² ≤ m³Σe². The direction is correct.
- **Two-base averaging** (both AveragedAssembly and AmbientAssembly): the square stays inside both the T and S0 averages, and there is no Jensen step. The S0 shift is removed by `Equiv.addRight` over the full ambient Hom space ΩT, and `card ΩS` cancels.
  - In the ambient version, the shift reaches the original ambient base through `a8_nested_actual_w6_energy_naturality`, which is in EnergyNaturality, outside this window but a native root.
- **A9 fibre** (`a9_ambient_fiber_card`): exactly `[a,i]₂[b,j]₂·2^{k(a−i)}·2^{k(b−j)}`.
  - The section kernel has dimension a−i and the extension quotient B0/B has dimension b−j.
  - The B0 count is Gauss(b, b−j), and the dual annihilator turns it into Gauss(b, j). That dual step is used only to show the two counts are equal.
  - `a9AmbientFiberEquiv` gives both inverse laws.
  - `a9Ambient_A8_sideConditions_iff_rank_preservation` is proved in both directions, so the fibre is exactly the A8 predecessor set.
- **W6 predecessor fibre** (`w6_actual_predecessor_frequency_fiber_card`): exactly `2^{2·rank X·l}`, universal over X and Z.
  - The backward map derives `w6Precedes` from the rank of the block candidate (`w6CanonicalBlockCandidate_rank_of_J_inj_P_surj`).
  - The forward map derives the displacement rank from `w6_precedes_actual_carrier_frequency_rank`.
  - No count premise is added.

**C4. A16 contract consumed by A20.**
- `filteredCarrierFunction_energy_le_A16` holds for every carrier `(A,B)`, every base `T` and every ambient width, under exactly two premises: `ComplexFourierSupportedThrough D f` and `UpToActualNormSqGlobal D eps f`. There is no cost premise.
- This answers proof-adversarial packet-2 F2 and complexity packet-2 Q2: the cost-free use in `a20_three_degree_global` is justified.
- The bound: (D+1) levels × 2^{10D²}, and D+1 ≤ 2^{D²}, giving 2^{11D²}.
  - Levels below the carrier cost are zero, by `selected_frequency_rank_lower_bound`, whose logic I checked.
  - Retained levels are orthogonal because their residual ranks differ (`retained_rank_representation` together with `typedComplexRankProjection_cross_orthogonal`, which is derived from Parseval and not assumed).
  - The zero-cost carrier `A=⊥, B=⊤` is handled through the order-0 restriction.
  - `eps ≥ 0` is derived from the premises, not assumed.

**C5. T1 transfer → typed W6.**
- `hactive_iff` closes by `rfl`. This means `typedW6Precedes C H X Z` is definitionally the same rank-additivity relation as `t1RankPrecedes`, in the same orientation, and `Z` is definitionally `t1OriginalRestriction`.
- Collisions are kept: `Finset.sum_eq_single` collapses only the parent variable `Z`.
- `t1PointwiseFull_fourierIdentity` is unconditional. Its uses inside this window go through the T1IndexTriple, `t1AmbientC`/`t1AmbientH` and `t1PullbackMap` API that A8Endpoint relies on.

## 3. Dispositions of HIGH and Medium findings

| ID (origin) | Severity | Disposition | Basis |
|---|---|---|---|
| P7-F1 / C7-F1 / N7-F1: `hHC` premise in the selected consumer | HIGH | **Resolved for the milestone's selected-leaf consumer. Retained as a non-claim for material-moment acceptance.** | `selected_leaf_HC46_original` is a native root with standard axioms. All three packet-1 lenses report it passing `original_HC46_exact` into the `hHC` slot of `selected_leaf_HC46_of_exact_PR` with no added premise. That slot has type `HC46ExactContract` (packet 7). Because the application compiles, `original_HC46_exact` has that type. **Logical availability:** the same term would also fill `hHC` of `selected_actual_material_moment_bound`. **Missing:** no compiled, hHC-free material-moment declaration exists. It is not among the 172 roots, and that theorem still requires `hSpectral : Spectral47ExactContract` plus `hfail`. This window has neither body, so the claim rests on prior reports, not on re-reading. |
| P7-F2 / N7-F2: HC46ExactContract self-contradictory or vacuous | HIGH | **Resolved.** | (a) A closed, standard-axiom proof `original_HC46_exact : HC46ExactContract` exists (native stdout plus the type argument above). A provable contract can't be refutable, so `hHC` consumers are not vacuous because the contract is false. (b) The proposed counterexample fails at the premise. All three packet-8 lenses independently state that `PseudorandomExact` uses a nominal budget padded with zero rows, and that `exactWholeRestriction` gives the whole nonempty fibre at every `r`. So the premise forces `eta ≥ mean b ≥ 0` (`boolean_mean_le_of_exact`). With `eta=0`, `b≡true` fails the premise. With `eta<0`, the premise is unsatisfiable, so `rpow` of a negative base is never reached. With `eta=0` and a valid b, `b≡false` on the whole space; packet 1 reports that `original_HC46_exact` treats `δ = min eta 1 = 0` by forcing f=0. **Caveat:** whether `HC46ExactContract` is faithful to the manuscript's HC4.6 is still open (manuscript gate). |
| P7/C7-F4, N7-F5: exact-r versus up-to-r | Medium | **Resolved at contract level.** | Padding makes `PseudorandomExact r` cover every actual order ≤ r. The HC46 contract is applied at levels `i ≤ r` with the same `r`, so no monotonicity lemma is needed. `PseudorandomExact` remains a **one-sided density upper bound** with constant `2e`, needs `r<d`, and nontrivial e is not shown. Nothing about a two-sided bound is claimed. |
| P9 F1/F2, N9 1/2: one-sided bound, exact budget only | Medium | **Retained as a claim boundary.** | Same as the row above. The strict guards (`r<d`, `b<k`, `targetRank<k` giving `binary_target_half`) are reported by three packet-9 lenses. Not re-read here. |
| P2-F4: real-q needs non-dyadic interpolation | Medium | **Resolved as out of scope for the milestone.** | All packet-1 lenses report that `manuscript_A22_actual` has natural `p`, `2≤p`, `p=2^k`, and real `q = pConjugate p = p/(p−1)` (packet 6). No arbitrary-real-p claim is made, and no interpolation is required. The A22 body is not in this window. |
| P4-F2 / C4-F1: overlap multiplicity charged in A11 | Medium | **Partially resolved.** | The costs as exposed are correct: the A8 cube ≤ 2^{6Dk} and the A9 multiplicity ≤ 2^{3D(i+j+k)} (`a7_a9_multiplicity_le`, numerics verified by packet 4). Whether A11 sums them against the A10 saving with the supported-window split is in an A11 body not supplied here (X1, X2). |
| P4-F3 / C4-F3 / N4-2: zero-parent `a7_a9_*` lemmas | Medium | **Resolved within bounded scope.** | No body in this window references them. The A8Endpoint route goes through A9AmbientFiber only. The bounded trace disposition says they are absent from the exact172 and focused-four closures. This is not an all-repository absence claim. |
| P5-F4 / N5-F2: A9InitialGraph is not the actual fibre | Medium | **Resolved within bounded scope.** | The actual fibre `A9AmbientFixedFinalFiber` keeps the `induces` equation and the original orientation (B ⊆ B0). Its count and partition equivalence are proved here. `a9_initial_datum_card` and `a9_fiber_triple` are absent from the trace (bounded). |
| P5-N1: unused `_horder` in A8Endpoint | Low | **Retained.** | The premise is harmless, but the consumer has to supply `a6Order t ≤ D`. |
| P5-F6: private names in public statements | Low | **Retained.** | `finalEnergy` and `a9AmbientA8Energy` are separate private definitions with the same body. A11 can only match them by unfolding (X1). |
| Stale or acceptance comments | Low | **No evidentiary weight.** | The AveragedAssembly and AveragedTransport headers ("accepted with notes against frozen run 46/56", "Full HC46 … uncertified"). The WeightedPredecessor docstring "still-needed fiber equivalence", which is proved later in the same file. The mid-file `end` and the `/- -/` comments. These neither certify nor invalidate native evidence. |

### New finding from this window

**W3-M1 (Medium, coverage boundary).** Several window files import project modules that are not in the all170 review selection:
- A9AmbientFiber imports `ActualBinaryMatrixHC46A9ActualFiber`;
- CommonA16 and FourierA16 import `…CommonDerivative`, `…MixedPeeling` and `…FinitePeeling` (opened);
- FullA16Final imports `…CommonDerivative`.

Packet 8 found the same pattern for GrassmannIncidence, TripleRestrictionRank, VectorAdvice and PosteriorReweighting.

These modules sit inside the native 319-file closure, so they are compiled and their axioms are standard. But no report in this campaign reviewed their bodies.

Along the visible final route (A8Endpoint, A9 count, A16 bound), I found no use of declarations from them. `rankProjection_inner_eq_zero` and `complexEnergy_finite_sum_of_orthogonal` are defined in the window files themselves. The mixed-peeling orthogonality theorems in FourierA16 and CommonA16 do depend on MixedPeeling, but I saw no use of them on that route.

**Needed:** confirmation from the qualified trace that none of the four focused consumers reaches a constant defined in a project module outside the 170. Otherwise, the prior review provenance of those modules. Until then, integration stays incomplete on this point.

## 4. Cross-window questions still open (not answerable from this window's source)

- **X1.** In the A11 body (`a11_weighted_mixed_sum_le_actual_final_fibers`, `a11_original_weighted_mixed_bound`, `manuscript_A7_actual`), confirm three things:
  - the summation-order swap from endpoint-indexed to A9-source-indexed, through `a9AmbientA8PartitionEquiv`;
  - the matching of `finalEnergy` with `a9AmbientA8Energy`;
  - that hS is discharged by genuine strict-lower-degree induction.
  
  Non-claims packet 1 also noted a docstring saying the A9 aggregate is "forthcoming"; that needs reconciling. Root's line-550/553/713 notes are hypotheses only.
- **X2.** How A11 discharges `hfin : a+b+k ≤ D`, `hi`, `hj` and `_horder`, and whether terms with `a+b+k > D` are removed by `a8_actual_energy_zero_outside_supported_window`.
- **X3.** The A18 → A21 → A22 dependency direction and constants (`9/512`, `196D²`, `200p²−100p`, `420→500`), and DR6's signed incidence and normalisation (`/162`, `6D²`, `7D(i+j)`, `31/225`). These were verified only in packets 2 and 6.
- **X4.** The typed A14 and A15 definitions and transports that A16 relies on (`canonical_source_rank_projection_energy`, `arbitrary_carrier_rank_projection_identity`, `actual_global_to_bottomTop_typed`). They are in packet 7/8 bodies.
- **X5.** In ActualLeafLabelRankImageAlignment and MatrixLiftNominalDirectComparison: that the same predrawn T/f carries through to the leaf lift, and the factor-2 comparison.
- **X6.** Whether OriginalActualInfluenceThrough's order-0 term matches the manuscript's influence definition (non-claims packet 2). This needs the manuscript.
- **X7.** W3-M1 trace confirmation.

## 5. Safe claim boundary

**Safe to state:**
- In this window's 12 bodies, kernel-checked on the stated native evidence with Init/Mathlib/Batteries trusted at their pinned versions:
  - the T1 ordinary/active bijection and the exact Fourier transfer, with no hypotheses;
  - the exact W6 predecessor fibre count `2^{2·rank X·l}`;
  - the A8 two-base averaged transport, with the square kept inside both base averages and a single cubic complement loss, giving the endpoint `E_T Q(output) ≤ 2^{6Dk}·Σ_{actual final predecessors} E_T[energy²]` under Fourier support (plus the unused `_horder`);
  - the exact actual A9 fixed-final fibre count and the A8↔A9 partition equivalence, with the coarse charge `2^{3D(i+j+k)+6Dk}` under `a+b+k ≤ D` and a proved zero lemma covering the complement;
  - the arbitrary-carrier A16 bound `2^{11D²}·eps` with no cost condition.
- The universal theorem `original_HC46_exact : HC46ExactContract` exists, so the contract is consistent. The selected-leaf HC46 consumer has no `hHC` premise.

**Not claimed:**
- Acceptance of the material moment, reduction, runtime or learning steps. `selected_actual_material_moment_bound` still needs `hSpectral` and `hfail`, and no dedicated hHC-free export exists.
- Spectral47; useful numeric NO bounds; nontrivial `e` in `ExactBudgetZoomBound`; any two-sided pseudorandomness.
- Source/star, robust8S (`AllAmbientInverse` is unproved), the encoded reduction, upstream builds and bridges, fresh-checkout replay, and final-provider gates.
- Manuscript rendering, fidelity or novelty.
- Zero *total* warnings. Zero owned warnings and zero inherited regressions are established; the inherited warning baseline remains open debt.
- That legacy helpers are absent anywhere beyond the exact172 roots and the focused four consumers.
- That every library body was newly reviewed.
- Any verdict on the full manuscript or on the full integration.
