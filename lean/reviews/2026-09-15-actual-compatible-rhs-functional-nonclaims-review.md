# Actual compatible RHS functional: non-claims-boundary review

2026-09-15. Top-level read-only review of commit `f740e503c3e357e9329fd5e6bbd1809ae0d26d37`, the frozen `ActualCompatibleRhsFunctional` main and Checks modules, and the associated target-fresh certification evidence. No Lean source, certification evidence, manuscript, release, push, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The increment proves two bounded existence/compatibility facts for actual-source good questions. First, an RHS-respecting linear functional exists on the selected coordinate space. Second, given any such functional for one good question, there is a unique RHS-respecting functional on another question's equation span, and the two functionals agree on the certified equation-span/coordinate-space intersection.

The uniqueness is confined to the equation-span functional `g`, where the selected equation vectors form a basis and determine its values. The coordinate-space functional `f` is obtained by a noncanonical extension and is only existentially quantified or supplied as input. The increment neither proves nor claims that a coordinate-space or ambient extension is unique.

This increment does not construct label objects, prove label gluing or transport, define an actual star carrier or acceptance predicate, establish clique-resampling stationarity, assemble a randomized reduction, establish source or target hardness, prove the manuscript headline theorem, or imply `P = NP` or `P != NP`.

## Frozen commit and evidence

The reviewed source commit is `f740e503c3e357e9329fd5e6bbd1809ae0d26d37` (`prove actual compatible rhs functional`). `git diff --exit-code` confirms that both reviewed source files match that commit.

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualCompatibleRhsFunctional.lean` | `5173EA699D41D0305508376F9EDEE99F8202FCD8C8EC134021BEE78366CD65CB` | Independently rehashed; matches both certification source snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualCompatibleRhsFunctionalChecks.lean` | `F3E5525D5BEACFFB2329E91377293DD1F781E6EB8F45C2DB3395BB40BA455ADA` | Independently rehashed; matches both certification source snapshots. |
| `research/evidence/2026-09-15-actual-compatible-rhs-functional-fresh-run/artifact-hashes.txt` | `D51204172B84D74FEC19BB6C34A6245F69AA4FF3A3D42EEE1A471261DFE21A30` | Independently rehashed; matches `artifact-hashes-manifest.sha256`. All 49 recorded rows were present and matched their recorded sizes and hashes. |
| `research/evidence/2026-09-15-actual-compatible-rhs-functional-fresh-run/closeout.md` | `9967119CD33907D199504355F6C170C60413A4C9F13573E2F4FAC2F501D0E313` | Wording and dependency boundary reviewed; no claim promotion found. |

The certification records exit code `0` for `ActualStarQuestionSupport`, `ActualStarSpanIntersection`, `ActualFinite3LinSource`, `ActualRhsFunctionalConstruction`, `ActualStarSideConditionAgreement`, the main module, and the Checks module. Their object hashes are respectively `8B4A75485327BA8836F8FDB1AB561ACD15DB816E8C7C16084C58DCEA0B9461FF`, `DECC2EAA887AC7C8C1DB4F121FC0B5A9BA03369FA191E1DE6B7CCA3FCE748DBD`, `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48`, `9A8526B28F205FD8153F9E43FB3A36DF374E6BADB4F7091C9C9721AFDA9D650F`, `856DD508D6668231A64F5FBF71DD2A535B1B079DE7A53EE5ED458320B5E50889`, `C7D44C65E4D790D0319A9C8295CB5C6B63446C501F79A3F1131D5A72E4EA124D`, and `5BBF75A4E8736747AEB15807894A279E2867DA064223157527F7383631807F64`.

The evidence describes a target-fresh sequential build under Lean `4.34.0-rc2` with `LEAN_NUM_THREADS=1`. The isolated target excluded all seven rebuilt project-module artifacts and used an immutable seeded transitive dependency tree. Source-before and source-after inventories agree, and source hashes were asserted after every compile stage. This supports the frozen increment within the stated dependency scope; it is not a complete from-source rebuild of Mathlib or the project.

The postprocessing failure is evidentiary bookkeeping only. `finite.stdout.log` and `finite.stderr.log` were both empty while `finite.exit.txt` recorded exit code `0`; the PowerShell pipeline therefore failed to create the expected empty `finite.combined.log`. Recovery created the missing empty combined log and reran postprocessing over the frozen sources and already-built objects without recompiling Lean. The recovered empty file has the standard SHA-256 for empty content and is covered by the final 49-row artifact manifest. This diagnostic does not change the compile result, but it should remain described as a recovery rather than a second clean certification run.

The forbidden scan reports no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit `axiom` declaration. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both exported theorems. Four warnings come from dependency modules; main and Checks emitted none.

## Exact proved boundary

`actual_exists_coordinateFunctional` starts with the previously certified unique RHS functional on `equationSpan I.support U`. `LinearMap.exists_extend` extends it to the ambient finitely supported vector space, and composition with the coordinate-space subtype produces a functional on `coordinateSpace I.support U`. The theorem proves that this `f` takes every selected equation vector to `I.rowRhs e`.

The extension step proves existence only. Different ambient or coordinate-space extensions may agree on the equation span while differing elsewhere. The theorem does not expose a canonical construction, prove independence from the choice made by `exists_extend`, or establish uniqueness of `f`.

`actual_existsUnique_compatibleRhsFunctional` takes a first-question coordinate-space functional `f` and its RHS equations as explicit inputs. It constructs the unique RHS-respecting equation-span functional `g` for the second good question using `actual_existsUnique_rhsFunctional`. The previously certified `actual_sideCondition_agree_on_intersection` proves agreement between `f` and `g` on

```text
equationSpan I.support U' inf coordinateSpace I.support U.
```

The `exists!` uniqueness follows from the RHS equations for `g`; intersection agreement is an additional certified property of that unique `g`. The statement does not quantify uniqueness over `f`, over extensions of `g` to a coordinate or ambient space, or over pairs of full labels. It also remains conditional on `GoodQuestion` for both `U` and `U'` and on the supplied `f` satisfying the first question's RHS equations. The companion existence theorem discharges the latter input only after a particular good question is supplied.

## Fixtures

The one-row fixture is nonvacuous for both exported statements. `oneRowU` contains one selected row with RHS `1`, and the actual-source support-cardinality theorem supplies its three-coordinate equation vector. The first example invokes exact coordinate-functional existence. The second first obtains such an `f`, then invokes the exact two-question compatibility theorem with `U = U'` and proves its full conjunction.

This is a strong theorem-signature fixture, but it is not a test of transport between distinct questions or a nontrivial partial overlap: setting `U = U'` makes the certified intersection the equation span inside the same coordinate space. The separate empty-question fixture covers the valid zero-dimensional existence branch. None of the fixtures constructs labels, a star edge, a sampler, or an acceptance experiment.

## Manuscript dependency and remaining boundary

The increment combines the earlier equation-span RHS construction with the earlier intersection-agreement theorem. It supplies the linear-functional compatibility needed before a minimal label representation can be defined, but it does not itself define the label type or prove that a complete label is transported, glued, sampled, or accepted.

The immediate legitimate consumer is a minimal label/gluing layer that records the relevant coordinate-space and equation-span data and uses this compatibility theorem at the overlap. The remaining path includes:

```text
define minimal labels and their exact equivalence relation
  -> prove label gluing/transport from the certified intersection agreement
  -> construct the actual star carrier and acceptance theorem
  -> prove clique-resampling stationarity and value/failure transport
  -> connect source completeness and soundness
  -> instantiate and verify the polynomial-time randomized reduction
  -> discharge fixed-parameter quantitative consumers
  -> reconcile the learning corollary and manuscript headline theorem
```

## Claims that remain prohibited

The accepted description is: **Lean proves existence of an RHS-respecting coordinate-space functional for each good actual-source question and, given one such functional, constructs the unique RHS-respecting equation-span functional for another good question that agrees with it on the certified intersection.**

Do not describe this increment as proving a unique coordinate-space or ambient extension, a canonical label, full label gluing or transport, an actual star construction, star acceptance, clique stationarity, a source-hardness instantiation, a randomized reduction, NP-hardness, manuscript completion, novelty or publication certification, `P = NP`, or `P != NP`.

The closeout's `PASS` wording, postprocessing-recovery disclosure, and explicit limitations are accurate for certification. This non-claims lens accepts the increment as one bounded bridge, subject to the other two required reviews and all remaining end-to-end obligations.
