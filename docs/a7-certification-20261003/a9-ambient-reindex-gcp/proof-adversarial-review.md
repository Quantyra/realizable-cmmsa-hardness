# Proof-adversarial review: S3132 ambient A9 reindexing

Verdict: **GO-WITH-NOTES**

No finding blocks bounded acceptance of the frozen actual-predecessor partition and fixed-final charge. This verdict does not certify the analytic A8 inequality, the full manuscript, or story closeout.

Reviewed 2026-10-04 as the top-level proof-adversarial lens under Quantyra-Planning `docs/formal-three-lens-closeout-protocol.md` and `docs/protocol.md` (especially lines 87?98, 139?146), with the S3132 scope recorded in `stories/S3126-realizable-hardness-formal-proof-and-paper.md`, lines 3284?3294. No nested reviewers were dispatched. No Lean, Lake, or elan was run locally. Only this report was created; source, Git state, and existing evidence were not modified.

## Frozen scope and evidence

The reviewed source files are `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean` and its `Checks.lean` module. References below use repository-relative paths and one-based source lines. The accepted evidence root is:

`docs/a7-certification-20261003/a9-ambient-reindex-gcp/session-20261004-reindex/`

The authoritative accepted run is `runs/cmmsa_a9_ambient_20261004T192626Z_83a1ebb0/`, identified by `report.json`. Earlier failed runs were not treated as accepted evidence.

Read-only SHA-256 verification matched the report for:

| Artifact | SHA-256 |
| --- | --- |
| Reindex source | `5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE` |
| Checks source | `82785615ADB3E40F10A47F78293090B3572C208764151D07E7E5C0F6C57A4F5C` |
| Accepted manifest snapshot | `89053E8B35F3F5D190B6B8FF6074C016284D05CD268AAA432E5439CCD5881670` |
| Accepted input archive | `36CA1D0129B554B2D4D811DB7D8CBBAE0D767DDC6964CF2ADB4336052A11EE8A` |
| Accepted evidence archive | `46DEFD1F5AB253BDF6468580555D383A793B3FE57CD60FC42E552A0E81320650` |

The two candidate files inside the input archive also match these source hashes. All 201 current project source files listed in the accepted manifest match their recorded hashes. The remote `source-before.json` and `source-after.json` agree; their project entries match the manifest, with three additional configuration entries. The manifest's earlier `frozen_identities` source hash is distinguished from the repaired `offered_identities`; the latter matches the accepted source and report. This is not evidence of an accepted-source mismatch.

Retained `remote-evidence/stage-{0,1,2,3}.command.json` and corresponding `.native-exit` files record exit 0 for dependency closure, source, Checks, and fresh axiom output. All eight stage stdout/stderr hashes match their command receipts. The three aggregate/finish exit files are also 0. The independent terminal receipt at `independent-terminal-20261004T194319Z-f27e5996/receipt.json` records terminated status for VM `8337954477286097405`. These are inspected historical compiler receipts, not a new compilation by this reviewer.

## Findings by severity

### HIGH / CRITICAL

None identified in the bounded increment. In particular, no contradictory premise, empty-only carrier, missing rank premise in the charge, false predecessor uniqueness, or nonstandard axiom dependency was found.

### MEDIUM ? analytic scope must remain bounded

**M1. The partition covers the A8 right-hand summands, not the A8 fourth-moment estimate.** References: Reindex lines 74?80, theorem `a9Ambient_A8_sum_partition` at lines 100?112, and `paper/body.tex` lines 1281?1294 (A8).

The equality partitions the sum of `E_T (typedW6OutputEnergy A B Y (filteredCarrierFunction A B T f))^2` over the stated actual predecessor carrier. Neither side is the mixed derivative's fourth moment on A8's left-hand side. The equality introduces no induction factor `2^(100(D-t)^2)` and establishes no T2 fourth-power graph-cost inequality. The charge theorems retain a supplied `2^(6Dk)` scalar; they do not derive that analytic cost. Calling this increment a proof of A8, HC46, positive-degree A7, or full manuscript certification would exceed its statements. **Does not block bounded partition/charge acceptance.**

**M2. The coarse charge is conditional on the final degree window.** References: Reindex lines 139?148, theorem `a9Ambient_fixed_fiber_coarse_charge`; manuscript `paper/body.tex` lines 1296?1299.

The explicit premise `hfin : a + b + k ? D` is necessary to invoke the imported multiplicity bound. The partition theorem is unconditional and also includes final maps outside this window. The increment does not establish their vanishing for a degree-supported input, nor discharge `hfin` for a downstream analytic application. Its lack of a Fourier-support premise is appropriate for an algebraic reindexing identity, but cannot itself justify the manuscript's ?nonzero terms require? assertion. A later composition must supply the support/vanishing argument or restrict the sum with justification. **Does not block bounded acceptance; prevents treating the present theorem as an unconditional global coarse analytic bound.**

### LOW ? evidence boundary

**L1. Historical zero-total-warning certification remains false.** References: accepted run `audit.json`, `prospective-audit.json`, and session `report.json` fields `legacy_zero_total_warning_green`, `warning_policy`, and `S3137`.

The legacy audit is preserved with its recorded hash `D957DD651228EC49A00FF4B3D4A38DD44EEA3C1FEC4B27C8A4699C4159D1267E`; it rejects the nonzero warning totals. The prospective audit records no new owned warning headers, no regression, and no shared-dependency source drift. The planning protocol explicitly treats frozen inherited warnings as separate S3137 debt. Compiler success and the prospective warning policy therefore support this bounded landing, but not a zero-warning or full certification claim. **Does not block bounded mathematical acceptance.**

## Mathematical adequacy audit

### Actual carrier and both directions

Reindex lines 28?35 store actual ambient `A0 ? A`, `B ? B0`, their dimensions `i` and quotient codimension `j`, and an actual linear map `X : B0 ? V/A0` of rank `k`. The two incidence equalities are exactly `A ? A1 = A0` and `B + B1 = B0`, where `A1` is the preimage of `range X` under `A0.mkQ` and `B1` is the ambient image of `ker X`. These match the A8 selector conditions in `paper/body.tex` lines 1279?1286. The imported definitions are `ActualBinaryMatrixHC46A9AmbientFiber.lean` lines 25?33 and 334?357.

The final map is the canonical quotient-after-restriction map `q_(A0,A) ? X ? inclusion_(B,B0)` (AmbientFiber lines 113?119), not a chosen coordinate label. The target at Reindex lines 37?41 ranges over actual maps `Y : B ? V/A` of rank `k`, retaining each actual fixed-final predecessor datum and its `induces` equation.

In the forward direction (lines 55?62), the two incidence conditions imply preservation of rank, so the induced final really has rank `k`. In the reverse direction (lines 63?66), the stored equation and equal ranks of `X` and `Y` recover both incidence conditions. The relevant imported statements are `a9Ambient_A8_sideConditions_iff_rank_preservation` (AmbientFiber lines 894?975) and `a9Ambient_fiber_A8_sideConditions` (979?987). Their finite-dimensional argument is sound: restriction cannot increase rank, quotient cannot increase rank, and equality of initial/final ranks forces the restriction to have the full image and the quotient to be injective on that image. All modules in this increment are finite-dimensional binary vector spaces.

The inverse laws at Reindex lines 67?72 retain `A0`, `B0`, and `X`; substituting the stored induction equation recovers the final-map label. Proof irrelevance accounts for proof fields. This asserts uniqueness of the label of a given predecessor, not uniqueness of a predecessor over a final map. Multiple predecessors remain separate fiber elements.

### Sum and normalization

`a9Ambient_A8_sum_partition` uses `Fintype.sum_equiv` with this two-sided equivalence. Its summand is preserved definitionally. The target is a dependent sigma, so its sum is mathematically the iterated sum over rank-`k` actual final maps and their fixed-final fibers. This is a genuine partition of the A8 right-hand predecessor sum for fixed `A,B,i,j,k`; it is not merely an injection or a normalized graph census. A future all-pairs/all-orders assembly is not exported here.

The energy is the required normalized squared L2 energy, hence fourth power of the L2 norm: `typedW6OutputEnergy` is the mean of `Complex.normSq` on the actual quotient/kernel output Hom (HybridW6Transport lines 286?293), and Reindex squares it before averaging over the original ambient `T`. `typedW6FourierDerivative_eq_actual` (HybridW6Transport lines 234?242) connects the Fourier expression to the actual derivative. `filteredCarrierFunction` (ActualTypedABCanonicalDCollapse lines 57?62) is the filtered affine restriction, not an arbitrary placeholder. `typedUniformMean` divides by the actual finite cardinality (HybridW6Transport lines 435?436). Both averaging Hom types contain the zero linear map, so no empty-average division hides the result. No extra cardinality factor is introduced by the reindexing.

### Vacuity and edge cases

The hypotheses are satisfiable at positive rank. For example, take `n=d=1`, `A=A0=0`, `B=B0=W`, `i=j=a=b=0`, `k=D=1`, and the nonzero map `X=Y : W ? V/0`. Both incidence equalities and `hfin` hold; the fiber has one predecessor. This is a direct mathematical witness, not a newly kernel-checked witness theorem. Thus the theorem is not restricted to empty or rank-zero cases. For impossible dimensions the uncharged partition legitimately equates empty sums. At `k=0`, rank-zero `X` is the zero map, the two graph powers are 1, and the fiber still counts the actual allowed subspace pairs. No positive-order exclusion is silently asserted.

### Exact and coarse graph-factor arithmetic

Let `E` denote the displayed averaged squared energy and

`M = [a choose i]_2 [b choose j]_2 2^(k(a-i)) 2^(k(b-j))`.

The imported `a9_ambient_fiber_card` (AmbientFiber lines 1221?1248) gives exactly `M`, with actual `B0` choices counted via `W/B` and Gaussian symmetry (lines 1089?1206). Section and extension counts are `2^(k(a-i))` and `2^(k(b-j))` (lines 992?1033 and 1038?1083). In particular, `j` is codimension in the original `W`; the extension dimension is `b-j`, not `j`.

Reindex lines 122?132 prove exactly `2^(6Dk) ? M ? E = M ? 2^(6Dk) ? E`. The scalar is present on both sides. No constraint on `D` is needed for that exact identity. The coarse theorem uses `a7_a9_multiplicity_le` (A7Transfer lines 3187?3190), namely `M ? 2^(3D(i+j+k))` under `hfin,hi,hj`, then multiplies by the nonnegative `2^(6Dk)E`. Its final exponent is precisely `3D(i+j+k)+6Dk`, by `pow_add`; neither graph factor is lost or counted twice. Nonnegativity is proved independently at Reindex lines 84?95. No sign hypothesis on the complex input is missing.

### Axiom leakage and statement checks

Checks lines 5?18 inspect all five public declarations. The retained fresh `stage-3.stdout` reports exactly `Classical.choice`, `Quot.sound`, and `propext` for each, including the equivalence and both charge theorems. It lists no `sorryAx`, application-specific axiom, or native-decide axiom. The accepted manifest's project-source forbidden-token entries are empty. This supports absence of leakage through the audited dependency chains; it is not a claim that every theorem in every imported module has been independently reviewed. The printed statements agree with the frozen source, including all exact/coarse rank and dimension premises.

## Certified scope and remaining gap

The accepted compiler evidence and this mathematical review support: the actual A8 predecessor-to-rank-`k`-final-map equivalence, the normalized energy-sum partition, nonnegativity, the exact fixed-final multiplicity charge, and its explicitly conditional coarse bound. The result consumes the actual ambient fiber and counts its members, rather than replacing it with a normalized carrier.

Remaining work includes the analytic A8 mixed fourth-moment inequality and degree-window discharge, composition of the partition/charges into the full weighted sum, A11/W6 aggregation, positive-degree A7, outward HC46/support and the later manuscript/reduction assembly. The session report explicitly disclaims full manuscript/story closeout. This report completes only the proof-adversarial lens for the frozen increment; separate required lenses, S3137 debt, and full-scope final reviews remain separate obligations.
