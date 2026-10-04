# Complexity-theory review: frozen A9 ambient reindex increment

Verdict: **GO-WITH-NOTES**

Reviewed 2026-10-04 as the top-level complexity-theory-reviewer for S3132. No finding blocks acceptance of the bounded partition and exact/coarse charge results. This verdict does not close S3132 or certify the manuscript. No nested reviewers were dispatched; no Lean, Lake, or elan was run locally. Only this report was created.

## Frozen scope and evidence

The reviewed source is `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean` (hereafter Reindex), with its Checks module, and the accepted run `cmmsa_a9_ambient_20261004T192626Z_83a1ebb0` named by `session-20261004-reindex/report.json`. Earlier failed attempts are not acceptance evidence for these bytes.

Read-only SHA256 checks matched all five report pins:

| Artifact | SHA256 |
| --- | --- |
| Reindex source | `5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE` |
| Checks source | `82785615ADB3E40F10A47F78293090B3572C208764151D07E7E5C0F6C57A4F5C` |
| Accepted manifest snapshot | `89053E8B35F3F5D190B6B8FF6074C016284D05CD268AAA432E5439CCD5881670` |
| Accepted input archive | `36CA1D0129B554B2D4D811DB7D8CBBAE0D767DDC6964CF2ADB4336052A11EE8A` |
| Accepted evidence archive | `46DEFD1F5AB253BDF6468580555D383A793B3FE57CD60FC42E552A0E81320650` |

The accepted input archive also matches the local bytes of Reindex, Checks, `ActualBinaryMatrixHC46A9AmbientFiber.lean`, `ActualBinaryMatrixHC46A7HybridW6Transport.lean`, and `ActualBinaryMatrixHC46A7Transfer.lean`. These imported statements were inspected as dependencies, not reviewed as new increments.

Under `session-20261004-reindex/runs/cmmsa_a9_ambient_20261004T192626Z_83a1ebb0/`, the four `remote-evidence/stage-*.native-exit` files and native/aggregate/finish exits are all zero. `remote-evidence/stage-3.stdout` prints the five reviewed declarations and their axiom profiles: only `propext`, `Classical.choice`, and `Quot.sound`. Checks lines 5?18 request those checks and axiom prints. The independent terminal receipt `independent-terminal-20261004T194319Z-f27e5996/receipt.json` records successful independent observation of TERMINATED. This review relies on preserved remote compiler evidence, not a fresh local build.

Protocol basis: Quantyra Planning `docs/formal-three-lens-closeout-protocol.md` (complexity pass criteria and argument/certification discipline), `docs/protocol.md` (mandatory complexity lens and warning-baseline rule), and owning `stories/S3126-realizable-hardness-formal-proof-and-paper.md`. The user?s single-report scope takes precedence over routine planning-update requirements.

## Findings, ordered by severity

### MEDIUM ? The original analytic A8 implication and complete induction are outside this increment

References: Reindex lines 28?71, 100?111, 115?166; `paper/body.tex:1263?1294`, equations A7/A8; `paper/body.tex:1311?1336`, equations A10/A11.

The source carrier is precisely actual `A0 <= A`, `B <= B0`, a rank-k map `X`, and the two A8 incidence equalities. The partition identifies this carrier with rank-k final maps and their actual inducing fibers. Its summand already is the final energy of `D_Y D_{A,B,T} f`; the theorem does not start from the preceding mixed derivative?s fourth moment and prove the A8 inequality. Nor does multiplying its sum by `2^(6Dk)` prove the T2 graph-cost estimate that supplies that multiplier upstream.

Consequently the increment closes the reindexing/charging gap for the actual A8 right-hand summands. It leaves the obligation to connect the original positive-degree decomposition to that RHS for arbitrary supported complex input, use the induction hypothesis on actual smaller spaces, and assemble all final-pair/rank/dimension sums. No removal of an overlapping-share premise, complete A7 hypercontractive theorem, or manuscript hardness theorem follows from these five declarations alone.

**Bounded acceptance:** not blocked. Claiming complete A8/A7 or manuscript certification from this increment would exceed its statement.

### MEDIUM ? The support guard and degree parameter must be discharged before ratio use

References: Reindex lines 136?146; `ActualBinaryMatrixHC46A7Transfer.lean:3187?3190` (`a7_a9_multiplicity_le`); `paper/body.tex:1276?1278`, `1296?1299`, `1311?1335`; `ActualBinaryMatrixHC46A7HybridW6Transport.lean:439?463`.

The coarse theorem requires `a + b + k <= D`, `i <= a`, and `j <= b`. The new theorem does not infer this mixed-order guard from Fourier support or nonzero energy. In particular, the corrected mixed order, rather than the enlarged ordinary order `a+b`, must justify the charge. The partition itself needs no degree guard, so its unconditional validity cannot discharge the coarse theorem?s hypothesis.

Lean?s `d` in `V d` is an ambient dimension. The charge?s separate `D` is the manuscript?s common degree bound. Substitution of the manuscript degree into `D` must be explicit; replacing it by an ambient dimension could destroy the intended constants and downstream ratios. This is especially relevant to induction over all finite spaces.

For fixed `t=i+j+k`, the surviving charge is `2^(3Dt+6Dk)`. Combined with the manuscript?s upstream `2^(24Dt)` and induction factor, this gives exactly `100(D-t)^2+27Dt+6Dk`. For `1 <= t <= D` and `k <= t`, the manuscript A10 arithmetic yields at most `100D^2-63Dt-4Dk`. The subsequent dimension sum and W6 weighting can therefore retain the manuscript?s decay. These are compatibility calculations, not additional Lean results of Reindex.

**Bounded acceptance:** not blocked. The guard and degree identification remain mandatory for a composed theorem.

### LOW ? Compiler and warning-policy success must remain distinct from certification closeout

References: `session-20261004-reindex/report.json` fields `bounded_acceptance_green`, `legacy_zero_total_warning_green`, `warning_policy`, `three_lens_reviews`, `full_manuscript_or_story_closeout_claim`; accepted `audit.json` and `prospective-audit.json`.

The accepted remote stages have zero errors and unsolved goals. The unchanged legacy audit still records `green=false`, `certified=false`, with the zero-total-warning requirement failing. The prospective audit records `green=true`, no new owned warning headers, no regressions, and no shared dependency source drift. This is consistent with the protocol?s frozen-warning-baseline rule, not a zero-warning audit. S3137 warning/certification debt remains.

The report?s historical ?three lenses not run? fields are preserved. This document supplies the complexity lens only; it does not retroactively supply the other lenses or rewrite evidence. The accepted audit?s claims boundary explicitly says S3132 remains open and S3137 incomplete. The owning planning story also separates bounded milestones from full assembly.

**Bounded acceptance:** not blocked under the recorded baseline policy. Full closeout still needs the required remaining reviews and certification obligations.

## Quantifiers, normalization, and multiplicity

There is no hidden existential choice of favorable `Y` or favorable input. For every finite binary ambient pair, every final `A,B`, all natural `i,j,k`, and every complex function `f`, the partition equivalence and sum identity hold. The final map is determined by quotient-after-restriction of `X`. The reverse direction uses rank preservation to recover both A8 side conditions (`ActualBinaryMatrixHC46A9AmbientFiber.lean:894?901`, `979?987`). Both directions retain actual predecessor data. This is not an injection into an unrelated count or a count conditional on an arbitrary supplied encoding.

For the charge, fix any `Y` of rank k, dimensions `a=dim A`, `b=codim B`, and allowed initial dimensions. The exact multiplicity is

`M = [a choose i]_2 [b choose j]_2 2^(k(a-i)) 2^(k(b-j))`.

The imported actual fiber census proves this value (`ActualBinaryMatrixHC46A9AmbientFiber.lean:1221?1247`). Reindex uses that census directly. The two graph exponents are multiplicities of initial data; `2^(6Dk)` is a separate analytic graph cost. Neither is dropped, inverted, or paid twice in these statements. The exact theorem holds for arbitrary D; only the coarse bound needs the mixed-order guard. The sharper manuscript assertion `M <= 2^(D t)` is not newly certified here; the certified coarse loss is the deliberately conservative `2^(3D t)`.

The source and target outer sums are counting sums, not uniform means over predecessor fibers or over rank-k final maps. Thus each fiber contributes `M * E(Y)`, not `E(Y)` and not `M/card(source) * E(Y)`. Conversely, the energy itself is normalized: `typedW6OutputEnergy` averages norm squares on the actual quotient/kernel output carrier (`ActualBinaryMatrixHC46A7HybridW6Transport.lean:285?306`), its square is the fourth-power L2 term, and `typedUniformMean` averages over all original linear bases T (lines 434?436). Reindex lines 74?81 keep these two normalizations intact. Reindexing never changes the T law or adds a rank-conditioning factor. It also does not itself prove the upstream shift/Fubini assertion in manuscript lines 1292?1294.

The `k=0` case is not silently removed. Exact multiplicity then reduces to the two Gaussian counts; at `i=j=k=0` it is one, with graph factor one. The partition can validly be empty for impossible ranks/dimensions. It is not vacuous in general: the zero initial/final map with bottom A0 and top B0 gives an actual zero-order predecessor whenever the stated nesting is used. Coarse-charge multiplication is justified by nonnegative energy (Reindex lines 84?94), including zero energy. For the positive-degree induction, the caller must exclude `t=0`; the new declarations do not impose that exclusion.

## Force assessment and ratio interface

This is useful structural bookkeeping with a real analytic interface. The substantive new connection is the bijection on the manuscript?s actual carriers and preservation of its actual energy summand. The exact charge then is a constant-sum/cardinality identity, and the coarse inequality imports the existing numerical bound. There is no new concentration, inverse theorem, computational reduction, switching decay, or asymptotic hardness force in this increment. Calling this only compiler theater would miss the carrier connection; calling it the force engine would also be inaccurate.

The charges can feed the A10/A11 coefficient budget and the normalized W6 estimate after the missing compositions and guards are supplied. The imported W6 theorem has a `2^(-6Dk)` weight and an explicit Fourier-support hypothesis (`ActualBinaryMatrixHC46A7HybridW6Transport.lean:439?463`). A positive graph charge by itself supplies no small bad/good ratio: the decay comes from the strict lower-degree induction and subsequent sums. Reindex contains no bad/good event comparison, denominator lower bound, or switching lemma. Consequently it provides a compatible loss term for downstream switching-quality ratios, not a certified switching-quality ratio or circuit/proof-system lower bound.

## Certified scope and remaining obligation

The bounded scope supported by the preserved compiler evidence and this complexity review is: actual A8-source/final-fiber equivalence, exact energy-sum partition, nonnegative normalized energy, exact fixed-final weighted charge, and coarse charge under the stated dimension/rank hypotheses. There are no HIGH or CRITICAL complexity findings.

The remaining manuscript obligation is to compose the general-complex-input A8 inequality, genuine lower-degree induction, support-based mixed-order guard, global reindexing and dimension/rank sums, and W6 contraction into the unconditional bounded analytic A7 theorem on the intended actual carriers. Its downstream decoder, reduction/runtime, asymptotic and headline theorem dependencies remain outside this increment. S3132 remains open; S3137 and full manuscript certification remain incomplete. Compiler success, this bounded theorem acceptance, owning-story closure, and full manuscript certification are four separate statuses.

Remaining work belongs to the existing S3132/S3137 scope and mandatory closeout protocol. This review creates no source changes, new evidence claims, or claim-boundary expansion.
