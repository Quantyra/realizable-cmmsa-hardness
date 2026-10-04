# Complexity-theory review: exact ambient A9 fiber

**Verdict: GO-WITH-NOTES.** The pinned candidate supplies genuine manuscript-facing finite combinatorial force: the actual fixed-final ambient predecessor equivalence, both inverse laws, the rank/A8 incidence correspondence, and the exact cardinality in manuscript (A9). It resolves the ambient-carrier counting gap identified in the accepted definition decision. It does not discharge analytic A9 reindexing, the A8 fourth-moment estimate, the A11 aggregate charge, or general positive-degree A7.

Reviewed on 2026-10-04 as the single top-level `complexity-theory-reviewer`. No delegation or subagents. This is one lens's verdict; it does not supply the proof-adversarial or non-claims verdicts, close S3132, or complete S3137.

## Exact scope and evidence identities

Repository: `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness`.

- Candidate: `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiber.lean`, SHA-256 `024850F649001829158FF0AB474CBFB7D8B228F6695EF673CB9EDF2D311226F9`.
- Checks: `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiberChecks.lean`, SHA-256 `C9C59633F0F34AA91CF28A47665AA78D3438406B63434796AB685C74181F3989`.
- Run: `docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z/runs/cmmsa_a9_ambient_20261004T090505Z_189bd32b`.
- Repair closeout: `docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z/compiler-repair-20261004T090127Z/report.txt` and `report.json`.

Both requested hashes were recomputed and match. The run's `remote-evidence/source-before.json` and `source-after.json` agree, including these two files and the inspected counting dependencies. Current `ActualBinaryMatrixHC46A9ActualFiber.lean`, `ActualBinaryMatrixHC46A9InitialGraph.lean`, and `ActualBinaryMatrixHC46A7PredecessorCount.lean` match their run pins. All four retained stdout/stderr pairs match the hashes in their stage command receipts. The evidence archive recomputes to `7577C17AD2586768A55BA7F2F5815B54230AA0AB7C6CF97C4F3E95A018498280`.

The existing compiler evidence supports exits `0/0/0/0`, zero errors and unsolved goals, and five fresh profiles containing only `propext`, `Classical.choice`, and `Quot.sound`. I read the fresh signatures and profiles in `remote-evidence/stage-3.stdout`; the Checks file checks the exposed declarations and prints axioms for the equivalence and four cardinality results. This review did not rerun the compiler. No `sorry`, `admit`, new axiom declaration, or unsafe/native-decision shortcut appears in the pinned candidate or Checks.

The legacy `audit.json` remains red solely for warnings. Its retained totals are 2271 warning occurrences across stages, including the frozen baseline of 748 inherited dependency warnings and 13 pre-existing owned style warnings; repair closeout reports zero new owned warning headers. The later written planning decision in [S3126](C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/stories/S3126-realizable-hardness-formal-proof-and-paper.md), lines 3266–3276, permits milestone review under that baseline/no-regression policy and leaves warnings as S3137 certification debt. This verdict neither rewrites the executed audit nor calls it strict-zero-warning green. The independent terminal receipt is `compiler-repair-20261004T090127Z/independent-terminal-20261004T091830Z-aa7f87a8/stdout`; it records the stopped builder. No cloud action was taken here.

## Why this has ambient A9 force

The relevant manuscript obligation is [paper/body.tex](../../../../../../paper/body.tex), lines 1269–1309, particularly (A8)'s selectors and (A9)'s fixed final `(A,B,Y)`. The authoritative route definition is [a9-ambient-definition-decision.md](../../../../a9-ambient-definition-decision.md). The pinned source implements that definition directly.

At source lines 25–33, `A0` is a subspace of the original `V` contained in `A` with dimension `i`; `B0` is a subspace of the original `W` containing `B` with quotient dimension `dim(W/B0)=j`. At lines 113–142, the datum retains the actual map

\[
X:B_0\longrightarrow V/A_0,
\qquad q_{A_0,A}\circ X\circ\iota_{B,B_0}=Y:B\longrightarrow V/A,
\qquad \operatorname{rank}X=k.
\]

The final `Y` is a parameter of the fiber, and `induces` is equality to that particular map. It is not replaced by its rank or an identity on an abstract rank space. Counting proof fields introduces no multiplicity of witnesses: they are propositions, and the extensional datum is `(A0,B0,X)`.

The target of `a9AmbientFiberEquiv` consists of actual sections over `range Y` and actual extensions of `Y.rangeRestrict` (lines 147–175). Forward reconstruction derives both from `X`. Restriction has the full image of `X`, and quotienting is injective on that image because both the initial and final ranks are `k` (lines 361–530). The section is unique **for that predecessor** through its required factorization of `X|B`; this is not a claim that all lifts of `range Y` are unique. The extension is `q X` with codomain restricted to `range Y`.

Conversely, the inverse sets `X=ell.comp psi` (lines 597–645). The section equation makes `ell` injective; the extension equation makes `psi` surjective since its restriction is `Y.rangeRestrict`. Thus `X` has rank `k` and induces the same actual `Y`. `a9Ambient_forward_factorization` reconstructs the entire original `X`, including its values outside `B`. `a9AmbientFiberEquiv` at lines 716–735 and the separate inverse laws at lines 752–770 recover the full datum and both affine factors. This is a two-sided equivalence, not a one-way charging injection.

The normalized module remains a dependency import, but the final ambient count is proved through these ambient affine fibers and actual Grassmann carriers. It is not a relabeling of `a9_normalized_actual_fiber_card`. That older normalized carrier has `X:(S × B/B0) → (S × A/A0)` and a distinguished identity restriction; it lacks the ambient fixed-`Y` equation (`ActualBinaryMatrixHC46A9ActualFiber.lean`, lines 25–37). No equivalence with that normalized product carrier is needed to accept this direct ambient result. Equal numerical counts still do not identify analytic derivative outputs.

Choices used in the counting proofs are legitimate: a temporary base section, base extension, and bases turn nonempty affine fibers into vector spaces (lines 1007–1019 and 1052–1069). They do not enter the ambient predecessor carrier or its inverse laws. The use of `Classical.choose` for the forward section is governed by the proved uniqueness. These choices do not hide a complement-dependent definition of the original fiber.

## Quantifiers, rank, selectors, and exact count

The count theorem at source lines 1221–1249 quantifies over arbitrary finite binary modules `V,W`, arbitrary subspaces `A,B`, and every actual `Y:B → V/A`, subject to

\[
a=\dim A,\quad b=\dim(W/B),\quad k=\operatorname{rank}Y,
\quad i\le a,\quad j\le b.
\]

`Module.Free`, `Module.Finite`, and `Fintype` are representation assumptions available for finite-dimensional vector spaces over `F=ZMod 2`; they do not impose an aspect ratio, positivity, full rank, or a chosen manuscript coordinate system. Natural-number indices already express nonnegativity. The equivalence needs finite dimension and `rank Y=k`; the cardinality additionally needs finite carriers. There is no assumed fiber cardinality, derivative inequality, desired final bound, or existence of the analytic shares in the hypotheses.

The fiber abbreviation alone does not assert `rank Y=k`: that crucial hypothesis is supplied by the equivalence and count theorem. It must remain visible in citations. Without it, the subtype can contain rank-losing predecessors and is not the A9 rank-preserving fiber. There is also no claim here about counting all maps inducing `Y` while allowing larger initial rank.

The A8 correspondence is exact. Source lines 335–357 define

\[
A_1=q_{A_0}^{-1}(\operatorname{range}X),\qquad
B_1=\ker X\ \text{embedded in }W,
\]

and the actual incidence equalities `A ∩ A1=A0`, `B+B1=B0`. The B equality is equivalent to `X(B)=X(B0)` (lines 774–825); the A equality is equivalent to injectivity of the quotient on `range X` (lines 829–891). `a9Ambient_A8_sideConditions_iff_rank_preservation` proves their conjunction iff `rank Y=rank X`, for data already satisfying the fixed-final equation (lines 894–975). Therefore every member of the rank-`k` fiber under `rank Y=k` satisfies both selectors, and conversely an inducing datum satisfying those selectors has rank `k`. Omitting selectors from the fiber's fields does not enlarge the intended count under the theorem's hypotheses. This settles the incidence correspondence, not the analytic inequality named (A8).

The count is exactly

\[
\left|\mathcal F^{i,j}_{A,B}(Y)\right|
=\genfrac{[}{]}{0pt}{}{a}{i}_2\genfrac{[}{]}{0pt}{}{b}{j}_2
 2^{k(a-i)}2^{k(b-j)}.
\]

Each section fiber has dimension `k(a-i)` after translation because the quotient kernel is `A/A0`. Each extension fiber has dimension `k(b-j)` after translation because its differences factor through the actual `B0/B` (lines 992–1084). In particular, `j` is **codimension of B0 in W**, and `dim(B0/B)=b-j`; it is not the dimension of `B0/B`.

`a9AmbientNestedB0Equiv` identifies actual containing subspaces with `(b-j)`-subspaces of `W/B` (lines 1089–1141). Annihilators prove only the scalar Gaussian symmetry `[b choose b-j]_2=[b choose j]_2` (lines 1146–1206). They do not substitute a dual quotient for the extension domain. The underlying `w6Gaussian` is the frame-product Gaussian number, with a proved actual Grassmann cardinality (`ActualBinaryMatrixHC46A7PredecessorCount.lean`, lines 745–798), not a placeholder defined to equal this new fiber's count.

This also matches the manuscript's kernel-complement description: any extension restricts to `Y` on `B`, its kernel meets `B` in `ker Y`, and `B+ker psi=B0`. Its kernel modulo `ker Y` is therefore the stated complement; the prescribed restriction determines the projection to `range Y`. No extra `GL(k,2)` factor is appropriate because `Y` itself fixes that identification. Image lift and extension determine `X` uniquely by the inverse construction.

Zero rank and zero-dimensional spaces are included. At `k=0`, each map is zero, and only the two subspace-choice counts remain. At `i=a,j=b`, there is one predecessor, `(A,B,Y)`. The theorem has no `t>0` or degree budget, correctly for an exact geometric census. In-range subspaces exist and the affine fibers are nonempty; the statement is not vacuous. Out-of-range indices are outside this count theorem's stated scope, and the intended A9 analytic window must supply the index restrictions.

## Downstream obligations and blockers to broader claims

There is **no blocking issue found for this exact ambient equivalence/count milestone**. The following are blockers to accepting the analytic chain or full theorem, not reasons to relabel the count as incomplete.

1. **Analytic A9 reindexing.** Connect the actual summation indices produced by A8/T1/T2 to this ambient fiber, preserving the final map and the derivative-fourth integrand, not just its rank. Prove the finite sum/fiber grouping and use the count for each fixed `(A,B,Y,i,j)`. Supply the support window `a+b+k≤D`, `t=i+j+k≤D`, and the positive-order truncation. The census includes `i=j=k=0`; A6/A11 exclude that initial term. Prove the ambient multiplicity/graph-weight bounds used by the consumer. The existing `a9_initial_datum_multiplicity_le` and `a9_initial_datum_graph_cost_le` concern normalized graph data (`ActualBinaryMatrixHC46A7Transfer.lean`, lines 3643–3679); their scalar bounds can be transferred using the matching exact formulas, but this does not transfer analytic summands. A source search finds no downstream Lean consumer of `a9_ambient_fiber_card` beyond its Checks.

2. **General-function A8.** Apply strict-lower-degree induction to the actual mixed derivative for every complex Fourier-supported input, then prove the T2/A1 passage to the selector-indexed final derivative sum with the correct graph fourth-power cost. Keep `s+k+u+v≤D`; the enlarged ordinary order `s+2k+u+v` may exceed `D` (manuscript lines 1273–1278). Prove intermediate-pair reconstruction and uniform shift/Fubini transport without additional multiplicity or rank conditioning (lines 1288–1294). The present module has no functions, moments, averages, or degree hypothesis, so it cannot certify any of these analytic assertions. Existing selected-energy bounds, including `a7_outer_hybrid_energy_sq_le_graph_power` at lines 7269–7292, do not identify a positive-order output pair share.

3. **A10/A11 aggregate charge and W6 consumption.** Combine the actual A6 weights, A8 cost, and ambient A9 multiplicities; establish the stated exponents and sums over `i,j,k`, including the separate `k=0` exclusion. Then reach the actual (A11) derivative sum. Its factorization `2^(-31D(k+1)-4Dk)=2^(-31D-29Dk)2^(-6Dk)` must be consumed by W6 on each actual `D_{A,B,T}f`, with the common degree bound `D` and the correct uniform measures. W6 is not wholly absent: `actualW6Derivative_weighted_fourth_moment_le_two` already has the weighted fourth-power estimate (`ActualBinaryMatrixHC46A7EnergyConsumer.lean`, lines 761–777). The outstanding step here is its source-faithful specialization, reindexing, and aggregate use, not declaring the ambient count to be W6. That file and `A7Transfer` were read as downstream interface evidence; they are not independently recertified by this A9 run.

4. **Unconditional positive-degree A7.** The existing `a7_positive_of_overlapping_shares` still assumes a family `e` satisfying `hfourth`, `hnn`, and `hshare` (`ActualBinaryMatrixHC46A7Transfer.lean`, lines 881–912). Construct and verify that family for general complex input, or prove the actual manuscript aggregate directly and discharge the equivalent consumer premise. Original pair shares exhaust `Q`, but shares on the smaller derivative's output space are not automatically original shares. The residual lower-order sum is explicit at lines 2506–2523. Zero-order output transport and preceding-character identities do not settle general positive-order output terms; fourth moments require control of interactions among frequencies. The existing order-one counterexample at lines 4905–4915 also blocks assigning a whole output `Q` to one original component. Complete the strict-lower-degree induction and terminal absorption only after this analytic bridge is established.

The manuscript locations for the aggregate and terminal step are `paper/body.tex`, lines 1310–1337. The ambient theorem's rank-preserving selectors are necessary inputs to that route, but neither a finite bijection nor an exact count supplies its nonnegative fourth-moment inequalities.

## Acceptance and claims boundary

This lens supports accepting the **actual ambient A9 equivalence, rank/A8 selector correspondence, and exact geometric census** once the other required milestone lenses complete under the written warning policy. It finds no false force or normalized-carrier substitution within that scope. The standing [formal-three-lens-closeout-protocol.md](C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/docs/formal-three-lens-closeout-protocol.md) still requires the separate verdicts and closeout record; this report does not invent their outcomes.

Permitted wording: “The fixed-final ambient rank-preserving predecessor fiber over `(A,B,Y)` is canonically equivalent to its section/extension carrier and has the exact A9 cardinality, with the A8 incidence conditions equivalent to rank preservation.”

Unsupported wording: “analytic A9 is complete,” “A8 is proved,” “the A11 charge is closed,” “general positive-degree A7/HC46 is unconditional,” or “S3132/S3137/the full realizable-hardness theorem is complete.” No hardness result, reduction/runtime witness, outward source construction, Theorem 1/Corollary 2 assembly, or P-versus-NP conclusion follows from this increment. S3132 remains partial and S3137 incomplete as specified by the latest S3126 planning entry.

The only file written in this review is this requested report. No Lean/source/Checks or warning evidence was edited; no Lean/Lake/elan invocation, cloud start, staging, commit, or push occurred. Existing worktree dirt was retained.
