# Actual star side-condition agreement: non-claims-boundary review

2026-09-15. Top-level read-only review of the frozen `ActualStarSideConditionAgreement` main and Checks modules and their target-fresh certification evidence. No Lean source, certification artifact, commit, push, release, or public claim was changed. This review file is the only artifact written by this lens.

## Verdict

**GO-WITH-NOTES.** The frozen increment proves that two supplied linear maps agree on the intersection of their domains when each map is separately assumed to return the same supplied right-hand side on the relevant equation vectors. It also specializes that implication to an `ActualOccurrenceAllocation.Instance` by using the instance's compiled support-cardinality and pair-intersection facts.

This is a valid conditional compatibility lemma. It does not construct either map, prove that a right-hand-side functional exists or is unique, construct or transport a label, define a star test or sampler, establish star acceptance or stationarity, instantiate source hardness, assemble a reduction, prove an NP-hardness result, resolve `P` versus `NP`, or establish manuscript or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Review result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualStarSideConditionAgreement.lean` | `4DB1C6998C63E028A85757A7EB0E25130CCCA9FD9D2DADAC2FD6D4FA0AE6E6B4` | Independently rehashed; matches the routed freeze and both certification source snapshots. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualStarSideConditionAgreementChecks.lean` | `8AE211FC034B96D777867334266F7893C8E2195BE0A45626A7F4AC4CB7C75489` | Independently rehashed; matches the routed freeze and both certification source snapshots. |
| `research/evidence/2026-09-15-actual-star-side-condition-agreement-fresh-run/artifact-hashes.txt` | `5D5C6BEF5DF070A4DD1CE07B32CDF4BCDB9333362A6339DA2AD9EDADA0A4C137` | Independently rehashed; matches `artifact-hashes-manifest.sha256`. All 32 listed evidence rows were present and matched their recorded sizes and hashes. |

The certification reports exit code `0` for the frozen question-support dependency, span-intersection dependency, main module, and Checks module. The fresh main and Checks objects have SHA-256 values `856DD508D6668231A64F5FBF71DD2A535B1B079DE7A53EE5ED458320B5E50889` and `BD9AB5C840BCCAD0047E4E516590E1CA31A6AAB8FFB7CF696E70E758D91B8B87`. The before/after source lists are identical, and the source-stability check passes.

The evidence describes a target-fresh sequential build with Lean `4.34.0-rc2`, `LEAN_NUM_THREADS=1`, and immutable seeded transitive dependency objects. The question-support and span-intersection modules were rebuilt in the new target before main and Checks. This certifies these frozen modules against the recorded dependency seed; it is not a full rebuild of all dependency sources.

The forbidden scan found no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit source-level `axiom`. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both exported theorems. No project-specific axiom is reported.

## Exact proved boundary

The generic theorem

```text
sideCondition_agree_on_intersection
```

takes a three-uniform linear incidence system, good questions `U` and `U'`, a supplied linear map

```text
f : coordinateSpace row U ->ₗ[ZMod 2] ZMod 2
```

and a supplied linear map

```text
g : equationSpan row U' ->ₗ[ZMod 2] ZMod 2.
```

Its `hf` and `hg` hypotheses require the respective maps to evaluate every equation vector in their questions to the same externally supplied `rhs`. For every

```text
z : equationSpan row U' ⊓ coordinateSpace row U,
```

the theorem concludes that `f` and `g` have equal values on the two domain embeddings of `z`.

The proof consumes the already compiled identity

```text
equationSpan row U' ⊓ coordinateSpace row U
  = equationSpan row (U' ∩ U)
```

and then proves equality on the span of the common equation vectors from equality on those generators. The conclusion is universal over the intersection, including the zero vector; it does not require the intersection to contain a nonzero vector.

The specialization

```text
actual_sideCondition_agree_on_intersection
```

uses `I.support`, `I.rowRhs`, `I.support_card`, and `I.pair_intersection` from an already supplied `ActualOccurrenceAllocation.Instance`. It removes the need for callers to pass the three-uniformity and pairwise-incidence assumptions separately. It introduces no producer theorem and does not show that an arbitrary external source can be converted into such an instance.

## Claims boundary

The strongest safe claim is:

> Lean proves that, for a good pair of actual-source questions, any supplied coordinate-space linear map and equation-span linear map that both respect the actual row right-hand sides agree on their shared subspace.

The words **supplied**, **both respect**, and **shared subspace** are necessary. The module proves an implication from `hf` and `hg`; it does not discharge those premises.

The theorem should not be described as proving existence of a right-hand-side functional. No theorem in this increment produces `f` or `g`, proves that the row right-hand sides are consistent with every linear dependency, or constructs an extension from the equation span to the coordinate space. It likewise does not prove uniqueness of a right-hand-side functional on either full domain. Its equality conclusion is only between the two supplied maps after restriction to the stated intersection.

The theorem also should not be called label construction or label transport. The generic domains here are `coordinateSpace row U` and `equationSpan row U'`; the module contains no manuscript leaf-label type, center-label type, affine/coset label, extension choice, equivalence class, or transport operator. The result can serve as a compatibility obligation inside a later transport construction, but it is not that construction.

No probabilistic object appears in the module. There is no distribution, kernel, resampling relation, clique, stationary measure, acceptance predicate, completeness probability, or soundness estimate. Therefore the increment supports no claim of star acceptance, clique-resampling stationarity, or preservation of the manuscript test value.

The actual-source specialization is structural rather than hardness-theoretic. It uses incidence properties of `ActualOccurrenceAllocation.Instance` and its `rowRhs`; it does not connect source optimum to a verifier, establish a completeness/soundness gap, prove a polynomial-time source producer, or assemble an encoded randomized reduction. It supports no source-hardness, NP-hardness, `P = NP`, or `P != NP` claim.

## Checks and limitations

The Checks module confirms the two exact signatures and prints their axiom profiles. Its general example shows that the actual-source theorem elaborates with caller-supplied good-question and right-hand-side hypotheses. The example includes an unused nonempty-intersection premise, correctly reflecting that nonemptiness is not required by the theorem.

The concrete one-row fixture compares zero maps at the zero intersection point directly. It does not invoke the exported theorem, exercise nonzero agreement, or test nonzero right-hand sides. This does not weaken the kernel-checked general proof, but it means the fixture is an elaboration smoke test rather than independent behavioral evidence. A future consuming module should use one nonvacuous fixture when it constructs the relevant maps; that improvement is not a condition for accepting this theorem.

## Remaining dependency path

This increment closes only the conditional agreement obligation. The claim-facing path still requires at least:

```text
existence and exact definition of the RHS-respecting maps
  -> label construction and side-condition-preserving transport
  -> concrete star/clique state spaces and resampling law
  -> star acceptance and stationarity/value preservation
  -> source completeness and soundness connection
  -> encoded polynomial-time randomized reduction
  -> fixed-parameter hardness statement
  -> learning corollary and manuscript reconciliation
  -> release and publication review
```

The completed theorem may be recorded in the authoritative obligation ledger as: **conditional agreement of two supplied RHS-respecting maps on `equationSpan U' ⊓ coordinateSpace U`, plus the actual-incidence specialization**. Its next consuming dependency should name the exact map-construction or label-transport theorem that supplies `hf` and `hg`.

## Prohibited claim promotion

Do not promote this increment to existence or uniqueness of an RHS functional, a label construction, a label-transport theorem, star acceptance, clique stationarity, actual-source hardness, a randomized reduction, NP-hardness of the manuscript target, manuscript correctness, novelty, publication readiness, `P = NP`, or `P != NP`.

The appropriate public status remains narrower: a kernel-checked actual-incidence compatibility lemma has passed target-fresh main-and-Checks certification, subject to the stated dependency-seed scope and the remaining construction and reduction obligations.
