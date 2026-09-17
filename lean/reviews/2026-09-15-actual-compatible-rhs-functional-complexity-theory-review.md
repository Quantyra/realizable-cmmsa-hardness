# Actual compatible RHS functional: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 actual-star algebraic bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment proves the intended compatibility composition. Every actual-source good question `U` admits a linear functional on `coordinateSpace I.support U` that takes each selected equation indicator to its stored right-hand side. Given such a functional for `U` and another good question `U'`, there is exactly one right-hand-side-respecting functional on `equationSpan I.support U'`, and it agrees with the coordinate-space functional on the certified intersection

```text
equationSpan I.support U' ⊓ coordinateSpace I.support U.
```

This combines the previously certified RHS-functional construction and overlap-agreement theorem without adding a satisfiability or consistency premise. It closes the local existence-and-compatibility bridge needed before defining transport. The defensible interpretation is limited to an intermediate coordinate-space functional and the unique compatible equation-span functional. `coordinateSpace` is the subspace of ambient functions supported on the variables occurring in `U`; it is not yet the manuscript's leaf domain `L + H_U`, and its functional is not yet a manuscript leaf label.

No acceptance predicate, probability distribution, sampler, encoded algorithm, running-time bound, PCP theorem, or reduction occurs in either new signature. The increment therefore carries no claim of efficient construction, source satisfiability, star acceptance, soundness, hardness, or a conclusion about P versus NP.

## Frozen artifacts and evidence

The reviewed Lean commit is `f740e503c3e357e9329fd5e6bbd1809ae0d26d37` (`prove actual compatible rhs functional`).

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualCompatibleRhsFunctional.lean` | `5173EA699D41D0305508376F9EDEE99F8202FCD8C8EC134021BEE78366CD65CB` | Matches the frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualCompatibleRhsFunctionalChecks.lean` | `F3E5525D5BEACFFB2329E91377293DD1F781E6EB8F45C2DB3395BB40BA455ADA` | Matches the frozen Checks source. |
| `research/evidence/2026-09-15-actual-compatible-rhs-functional-fresh-run/artifact-hashes.txt` | `D51204172B84D74FEC19BB6C34A6245F69AA4FF3A3D42EEE1A471261DFE21A30` | Independently rehashed evidence manifest. |
| `research/evidence/2026-09-15-actual-compatible-rhs-functional-fresh-run/closeout.md` | `9967119CD33907D199504355F6C170C60413A4C9F13573E2F4FAC2F501D0E313` | Certification receipt reviewed. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript dependency assessed, especially lines 171--187. |

The target-fresh certification rebuilt the frozen support, span-intersection, finite-source, RHS-construction, and side-condition-agreement modules, followed by the frozen main and Checks modules. All seven stages exited zero under Lean `4.34.0-rc2` with `LEAN_NUM_THREADS=1`. The target contained none of those seven objects before compilation. The main and Checks object hashes are `C7D44C65E4D790D0319A9C8295CB5C6B63446C501F79A3F1131D5A72E4EA124D` and `5BBF75A4E8736747AEB15807894A279E2867DA064223157527F7383631807F64`. Source stability and the independent evidence rehash passed.

This was a target-fresh rebuild of the direct project dependency chain against immutable seeded transitive dependencies, not a from-source rebuild of Mathlib or the entire repository. Four warnings came from dependency modules; main and Checks emitted none. The forbidden scan found no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit source-level axiom declaration. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both new theorems.

## Exact claim and assumption audit

### `actual_exists_coordinateFunctional`

The theorem assumes only an actual occurrence-allocation instance, a finite row set `U`, and `GoodQuestion I.support U`. It invokes the already certified unique RHS functional `psi` on `equationSpan I.support U`, extends `psi` noncomputably to the full ambient function space using `LinearMap.exists_extend`, and restricts that extension to `coordinateSpace I.support U`.

The result is existence, not uniqueness, of the coordinate-space functional. Values outside the equation span are unconstrained, so neither the proof nor the mathematics supports unique extension. Arbitrary stored right-hand sides are allowed because good-question equation indicators are independent. That local fact does not imply that the original overlapping 3-Lin instance has a satisfying assignment.

### `actual_existsUnique_compatibleRhsFunctional`

The theorem assumes actual good questions `U` and `U'`, a supplied coordinate-space functional `f` for `U`, and the premise that `f` realizes the stored RHS on each selected equation vector. It obtains the already certified unique RHS functional `g` on `equationSpan I.support U'` and applies the already certified intersection-agreement theorem. The latter uses the actual three-coordinate and pairwise-intersection facts together with both `GoodQuestion` premises.

The uniqueness is uniqueness of `g` on `equationSpan I.support U'`. It is not uniqueness of `f`, of an ambient extension, of a functional on a future `L + H_U` leaf space, or of a transport operator. The agreement conclusion applies exactly on the displayed intersection. It does not define a glued map on a sum, prove representative independence, or supply an inverse transport.

The Checks module supplies three useful interface witnesses: a nonzero-RHS one-row coordinate functional, a nonzero-RHS same-question compatibility composition, and the empty-question boundary. The same-question fixture has a nontrivial equation vector and RHS `1`, so the compatibility conclusion is not vacuous. The fixtures do not exercise distinct nonempty `U` and `U'`; the general theorem and its compiled dependencies cover that signature, so this is a coverage note rather than a mathematical blocker.

## Manuscript dependency

The manuscript's imported star contract says that `H_U` is the equation-indicator span, that labels on `L + H_U` realize the equation RHS on `H_U`, and that equivalent leaf vertices have unique side-condition-preserving label transport. The present result discharges the local linear-algebra compatibility required by that sentence:

```text
actual support structure + GoodQuestion(U)
  -> unique RHS functional on H_U = equationSpan(U)              [previously closed]
  -> existence of an RHS-respecting functional on coordinateSpace(U) [closed here]

GoodQuestion(U), GoodQuestion(U'), and an RHS-respecting f on coordinateSpace(U)
  -> unique RHS functional g on equationSpan(U')                 [composed here]
  -> f = g on equationSpan(U') ⊓ coordinateSpace(U)             [composed here]
  -> define and prove a glued functional on the relevant sum      [open]
  -> realize the manuscript leaf spaces L + H_U                   [open]
  -> define minimal label transport, inverse, and descent         [open]
  -> construct the actual star carrier and prove honest acceptance [open]
  -> prove clique-resampling stationarity and completeness         [open]
  -> supply soundness, formula compilation, and reduction assembly [open]
  -> fixed-L hardness and learning corollary                       [open]
```

The new theorem is therefore a necessary local bridge, but it does not replace the imported MZ transport contract in manuscript lines 171--187. In particular, the manuscript uses auxiliary transverse subspaces `L`, equivalence classes of leaf vertices, representative resampling, and restriction to a center space `K`; none of those objects appears here.

## Complexity and claims boundary

1. **No algorithmic efficiency.** The module is explicitly noncomputable and uses `LinearMap.exists_extend`, whose proof relies on classical basis extension. No representation of the chosen functional, algorithm to compute it, FP witness, circuit, Turing machine, or polynomial bound is supplied.

2. **No source satisfiability.** Local RHS realization on an independent selected set does not provide one global variable assignment satisfying the source. It does not prove the source YES promise or remove the need for the separately tracked source-failure analysis.

3. **No manuscript label transport.** A coordinate-space functional can serve as an algebraic precursor to a label, but the leaf space `L + H_U`, its label type, equivalence relation, transport map, uniqueness in the intended category, inverse law, representative independence, and descent remain undefined or unproved.

4. **No star acceptance or stationarity.** There is no actual center/leaf carrier, honest labeling, restriction-to-center test, clique-resampling kernel, stationary marginal, rejection sampler, or coupling of the source-failure estimate to every sampled block.

5. **No soundness or reduction.** The smooth/advice outer game, modified-star decoder and soundness theorem, HN formula compilation, concrete CMMSA promise distribution, encoded polynomial-time seeded map, random-coin and size bounds, source-hardness instantiation, fixed-`L` asymptotics, and learning transfer remain open.

The accepted public claim should remain:

> Lean verifies that every actual good question admits an RHS-respecting functional on its coordinate-support space, and that for a second actual good question there is a unique RHS functional on its equation span compatible with any such first functional on the certified intersection.

Do not strengthen this to a unique coordinate-space or ambient extension, a manuscript leaf label or label-transport theorem, an efficient construction, a satisfying assignment, star acceptance or stationarity, PCP soundness, a randomized reduction, NP-hardness, the manuscript headline theorem, novelty, publication readiness, `P = NP`, or `P != NP`.

## Disposition

**GO-WITH-NOTES.** Accept the two frozen claims as the canonical completion of the compatible RHS-functional bridge. The next theorem should use the certified intersection equality to construct the minimal glued functional on the exact sum space consumed by manuscript label transport, while freezing its domain, equivalence relation, uniqueness statement, and immediate consumer before implementation. Actual leaf-space realization, transport/descent, star acceptance, stationarity, and every hardness or efficiency claim remain open.
