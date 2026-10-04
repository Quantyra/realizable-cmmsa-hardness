# Non-claims-boundary review: exact ambient A9 candidate

Date: 2026-10-04. Reviewer: `non-claims-boundary-reviewer`, separate top-level review. No delegation or reviewer spawning occurred.

**Verdict: GO-WITH-NOTES.** The exact candidate supports bounded wording about its actual fixed-final ambient fiber, section/extension equivalence, inverse laws, rank/A8 incidence correspondence, and stated cardinality. No blocking claim inflation was found in the compiler-repair report or current A9 planning milestone. The notes below must accompany closeout wording. This verdict completes only this lens; it does not accept the milestone on behalf of the other reviewers, close S3132, certify S3137, or authorize a stronger public claim.

## Exact scope and evidence identities

Repository: `C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness`.

| Artifact | Independently read SHA-256 |
| --- | --- |
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiber.lean` | `024850F649001829158FF0AB474CBFB7D8B228F6695EF673CB9EDF2D311226F9` |
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiberChecks.lean` | `C9C59633F0F34AA91CF28A47665AA78D3438406B63434796AB685C74181F3989` |

Evidence paths below use these exact repository-relative prefixes:

- `SESSION`: `docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z`.
- `RUN`: `SESSION/runs/cmmsa_a9_ambient_20261004T090505Z_189bd32b`.
- `REPAIR`: `SESSION/compiler-repair-20261004T090127Z`.
- `CAPTURE`: `SESSION/captures/capture-compiler-repair-20261004T090127Z`.

Read the complete candidate and Checks, `REPAIR/report.txt`, `report.json`, `static-repair.json`, `workflow-context.json`, `starting-evidence.json`, source/Checks pre-repair snapshots, and the relevant preservation/diagnostic records. Read `RUN/audit.json`, stage command receipts and raw diagnostics, fresh Checks/axiom output, source/configuration and dependency inventories, terminal evidence, and `CAPTURE/manifest.json` with its pre-run repair-basis logs. Independently hash-checked the archive and stage logs. The retained independent VM observation is `REPAIR/independent-terminal-20261004T091830Z-aa7f87a8/{command.json,stdout,stderr}`; it reports VM ID `8337954477286097405` as `TERMINATED`. This review made no live cloud query.

Planning context read: the A9 route/stop-loss and latest compiler-green milestone in `C:\Users\Dan\Desktop\Projects\IGH\Quantyra-Planning\stories\S3126-realizable-hardness-formal-proof-and-paper.md`, relevant S3132/S3137 boundary entries, and `docs/formal-three-lens-closeout-protocol.md`, `docs/local-codex-workflow-protocol.md`, and `docs/claim-boundary-expansion-protocol.md` in that planning repository. This is an audit of the present A9 milestone and relevant boundaries, not certification of every historical entry in those long story files.

Additional mathematical context: `docs/a7-certification-20261003/a9-ambient-definition-decision.md`, `a9-ambient-author-report.md`, and `paper/body.tex:1269-1311`. Dependencies read for this lens include the normalized carrier boundary in `ActualBinaryMatrixHC46A9ActualFiber.lean:1-37` and the actual Grassmann carrier/Gaussian counting definitions in `ActualBinaryMatrixHC46A7PredecessorCount.lean:644-646,670-672,769-797`. Imported theorem names or earlier normalized-fiber evidence are not substituted for the new ambient theorem.

## What the declarations support

All mathematics here is over `F = ZMod 2`. The actual datum retains submodules `A0 ≤ A` in `V`, with `dim A0 = i`, and `B ≤ B0` in `W`, with `dim(W/B0) = j`, together with `X : B0 →ₗ[F] V/A0` and the fixed-final equation

```text
q_(A0,A) ∘ X ∘ inclusion_(B,B0) = Y.
```

`A9AmbientFixedFinalFiber` adds `rank X = k`; the equivalence and fiber conclusions require the explicit hypothesis `rank Y = k`. The input `(A,B,Y)` remains fixed throughout. `a9AmbientFiberEquiv` (source lines 715-735) is a two-sided equivalence with the dependent section/extension carrier over `range Y`. Its inverse composes the supplied section and extension. Both inverse laws and reconstruction of the fixed-final equation are declared and checked. This supports an actual ambient fiber bijection, not merely the earlier normalized product-map count.

`a9Ambient_A8_sideConditions_iff_rank_preservation` (893-975) proves, on a datum already satisfying the fixed-final equation,

```text
(A ∩ A1 = A0 and B + B1 = B0) ↔ rank Y = rank X,
```

where `A1` is the ambient preimage of `range X` and `B1` is the ambient image of `ker X`. `a9Ambient_fiber_A8_sideConditions` supplies these incidence equalities for the rank-matched fiber. This is the stated A8 selector/rank correspondence, not the manuscript's analytic inequality tagged A8.

The exact final theorem `a9_ambient_fiber_card` (1219-1249) assumes the displayed `AddCommGroup`, `Module`, `Module.Free`, `Module.Finite`, and `Fintype` instances for `V,W`, together with

```text
a = dim A, b = dim(W/B), k = rank Y, i ≤ a, j ≤ b.
```

It proves

```text
card(A9AmbientFixedFinalFiber V W A B Y i j k)
  = w6Gaussian a i * w6Gaussian b j
      * 2^(k*(a-i)) * 2^(k*(b-j)).
```

Here `b` is the codimension of final `B`, not `dim B`. The actual quotient `B0/B` has dimension `b-j`; `a9AmbientNestedB0Equiv` retains that variance. Gaussian symmetry changes the numerical count to `w6Gaussian b j`. It does not identify the actual quotient with a dimension-`j` normalized carrier or silently substitute a dual for an extension domain. The Gaussian dependency is the binary frame-product quotient, with its proved Grassmann cardinality interpretation.

The carrier comments correctly exclude chosen bases/complements/splittings as carrier data. Counting proofs do use temporary lifts/extensions, finite bases, and classical choice; the annihilator is used for numerical Gaussian symmetry. Accordingly, “canonical carrier/equivalence” is acceptable; “choice-free proof,” “axiom-free,” or “efficient constructive algorithm” would exceed the evidence.

## Compiler evidence and warning-policy boundary

| GCP stage | Exit | Warnings | Errors | Unsolved |
| --- | --- | --- | --- | --- |
| Dependency closure | 0 | 748 | 0 | 0 |
| Ambient source | 0 | 761 | 0 | 0 |
| Ambient Checks | 0 | 761 | 0 | 0 |
| Fresh axiom output | 0 | 1 | 0 | 0 |

Checks contains 40 `#check` commands and five `#print axioms` commands. All five requested profiles—`a9AmbientFiberEquiv`, `a9Ambient_section_fiber_card`, `a9Ambient_extension_fiber_card`, `a9Ambient_nested_B0_card`, and `a9_ambient_fiber_card`—are exactly the standard `propext`, `Classical.choice`, `Quot.sound` set. These are profiles of those exports, not an axiom audit or theorem-completion claim for the whole repository. Declaration checks establish the checked statements exist; they do not supply downstream analytic implications.

The source/Checks hashes match the captured and executed identities. All 163 captured project source hashes match the live source files and remote before/after inventories; the three captured configuration hashes also match. The 11,574 package and 2,520 core source identities agree with the immutable dependency baseline after hexadecimal case normalization. All four stdout/stderr hashes match their command receipts. Comparing the pre-repair source snapshot confirms that only `simp only [Nat.cast_id]` was inserted into the existing final-cardinality proof; Checks is byte-identical. This repair adds zero declarations/helpers and does not widen any statement or discharge an additional downstream obligation.

`RUN/audit.json` remains **red**, with `green: false`, `certified: false`, and the sole failure `Warnings/errors/unsolved goals are not all zero`. Its 2,271 warning occurrences aggregate replayed stages; they are not 2,271 distinct defects. The controller exit is 1 for that legacy warning gate. Remote stage/aggregate/finish exits are 0. Neither result should be erased or described as an entirely green audit.

The current planning workflow's “Warning-baseline certification rule” (lines 10-15) separately permits bounded acceptance/milestone review with zero new owned warning headers and a frozen source/configuration baseline without regression. It explicitly retains warning debt for S3137 and requires preservation of any executed zero-total-warning audit. Its current SHA-256 is `BA7737D8350DC66557CD9B548DD4BBA77D797525BFCB2A5777497C40297A2E0A`; the repair's historical workflow-context pin is `BBC9CA7E7F5CF3467B0D6F3C172C50D3F753416C08CBD6B399AE350F0D6BA50A`. These are different policy snapshots, not interchangeable evidence that the old audit passed.

Read-only comparison with `CAPTURE/repair-basis/stage-1.{stdout,stderr}` confirms the 748 inherited warning occurrences plus 13 pre-existing owned style warnings. Source and Checks warning-header multisets match that baseline; other stages introduce no additional headers. The report's raw comparison records one different overall header per stage because the cslib local-changes warning contains the new run directory. Normalizing only that run-directory name resolves the difference; substantive warning headers are preserved. Zero new owned warnings does **not** mean zero owned warnings, zero total warnings, warning cleanup, or pristine dependencies. Full certification must discharge the debt or record the explicit final decision required by the planning policy. No warning evidence was changed in this review.

## Notes and remaining closeout blockers

1. **Evidence-pointer correction:** S3126 line 3276 prints a 65-character archive “SHA-256,” `7577C17AD2586768A55BA7F2F55815B54230AA0AB7C6CF97C4F3E95A018498280`. The actual 38,249,530-byte `RUN/cmmsa_a9_ambient_20261004T090505Z_189bd32b-evidence.tar.gz` independently hashes to **`7577C17AD2586768A55BA7F2F5815B54230AA0AB7C6CF97C4F3E95A018498280`**. Repair `report.txt`, `report.json`, and terminal evidence use the correct value. Correct the planning pointer before reusing it in a final evidence record; no planning file was edited here.
2. **Minor comment scope:** the comment at source lines 750-751 describes a section/extension carrier although `a9Ambient_left_inverse_law` quantifies over a fixed-final fiber element. The comment at 772-773 summarizes both A8 conditions although the immediately following theorem proves only the B-side range equivalence; the full correspondence is at 893-975. The checked signatures are authoritative. These comment mismatches do not invalidate the bounded wording above, but should not be copied as broader theorem descriptions. Source edits are outside this review's authority.
3. **Status/policy separation:** repair `NOT ACCEPTED` and strict README/audit language are historical records of the executed gate. Current S3126 lines 3266-3276 correctly say compiler-green, eligible for review under the separate baseline decision, and not yet accepted. Keep both records. Earlier S3132 stop-loss entries describe earlier interfaces; the accepted definition decision and exact current declarations supply the present scope. A policy change is not a mathematical theorem, a helper increment, or evidence of full certification.

There is no blocker to the bounded non-claims wording in this report. Milestone acceptance still requires the separate top-level proof-adversarial and complexity reviews and the owning acceptance decision over these exact bytes. This report invents no verdict for those lenses. Whole-story/route-final closeout is not supported: analytic A9 reindexing, the analytic A8 obligation, A11/full weighted W6, positive-degree A7, remaining HC46/outward support, encoded reduction/runtime, manuscript assembly, and required final reviews remain separate obligations. S3132 remains partial; S3137 remains incomplete, including warning-policy debt.

## Claims that this evidence cannot support

- A switching lemma, arbitrary AC0/bounded-depth formula collapse, or a circuit lower bound.
- Full HC46/Lemma 4.6, its universal hypercontractive inequality, or discharge of its remaining applicability/analytic hypotheses. `HC46` in a module name is contextual naming.
- Full analytic A9 reindexing, manuscript A8, full W6, positive-degree A7, or the manuscript's degree-dependent bound following the A9 count. This theorem has no degree/energy/Fourier-average assertion.
- A Frege, bounded-depth Frege, PHP, or other proof-system lower bound/collapse.
- P=NP, P≠NP, an NP/circuit lower bound, a general SAT solver, unconditional CMMSA hardness, or completion of Theorem 1/Corollary 2.
- Warning-free/axiom-free certification, certification of all 163 modules' intended manuscript claims, completion of S3132/S3137, or publication/claim-boundary expansion approval.

## Proposed bounded closeout language

> The exact ambient A9 source `024850F649001829158FF0AB474CBFB7D8B228F6695EF673CB9EDF2D311226F9`, with Checks `C9C59633F0F34AA91CF28A47665AA78D3438406B63434796AB685C74181F3989`, has preserved GCP compiler evidence from `cmmsa_a9_ambient_20261004T090505Z_189bd32b`: stages 0/0/0/0, zero errors/unsolved goals, and five standard axiom profiles. Under the stated finite binary-module, dimension, rank, and index hypotheses, it proves the actual fixed-final `(A,B,Y)` fiber's section/extension bijection, both inverse laws, the A8 incidence/rank correspondence, and exact cardinality `w6Gaussian a i * w6Gaussian b j * 2^(k*(a-i)) * 2^(k*(b-j))`.
>
> Non-claims review is GO-WITH-NOTES for that bounded scope. Milestone acceptance remains subject to the other required reviews and the owning decision. The frozen 748 inherited and 13 pre-existing owned warning baseline has no new owned headers; the executed zero-total-warning audit remains red and S3137 warning debt remains explicit under the separate planning policy. S3132 is partial and S3137 incomplete. No analytic A9/HC46, switching, Frege/PHP, P-vs-NP, full hardness, or manuscript-completion claim follows.

Only this requested report was written. No Lean/source/Checks edits, Lean/Lake/elan execution, cloud start, warning-evidence modification, staging, commit, push, or dirt cleanup occurred.
